let array_map_option f arr = 
  let exception NoneFound in
  try 
    Some (Array.init (Array.length arr)
    (fun i -> 
      match f arr.(i) with
      | Some a -> a 
      | None -> raise NoneFound
    ))
  with NoneFound -> None

let rec pack_lambda l e = 
  match l with 
  | [] -> e 
  | (annot,ty)::xs -> pack_lambda xs (EConstr.mkLambda (annot, ty, e))
  

let push_e_rel_assums l env =
  let rec helper l env = 
    match l with
    | [] -> env
    | x::xs -> helper xs (Termops.push_rel_assum x env)
  in 
    helper l env

(* get the target of a nested Prod and its env. also lifts field_to_lift on its way *)
let rec constructor_target env term field_to_lift =
  let sigma = Evd.from_env env in
  match EConstr.kind sigma term with
  | Prod (name, ty, target_type) ->
      constructor_target
        (Termops.push_rel_assum (name, ty) env)
        target_type
        (EConstr.Vars.lift 1 field_to_lift)
  | t -> (env, term, field_to_lift)

(* get the ith field of a nested Prod and the rest of the prod and the env  *)
let rec get_ith_field_type env term i =
  let sigma = Evd.from_env env in
  match EConstr.kind sigma term with
  | Prod (name, ty, target_type) ->
      if i == 0 then (env, ty, term)
      else
        get_ith_field_type
          (Termops.push_rel_assum (name, ty) env)
          target_type (i - 1)
  | _ -> raise Not_found

let rec is_dependent sigma term i =
  if i <= 0 then false
  else if Termops.dependent sigma (EConstr.mkRel i) term then true
  else is_dependent sigma term (i - 1)

let annot_of_string_numbered s i r = 
  Context.make_annot (Names.Name.mk_name (Nameops.make_ident s (i))) r


type extraction = 
  (* The end of extraction is reached *)
  | Id 
  (* (constructor from to extract with universe, arg index to extract, nested further extraction) *)
  | Extraction of ((Names.constructor * EConstr.EInstance.t) * int * extraction)

let rec extraction_to_pp env sigma extraction = 
  match extraction with 
  | Id -> Pp.str "Id"
  | Extraction ((c,_), i , extraction) ->(
    let nested_extraction_str = extraction_to_pp env sigma extraction in 
    Pp.(
      str "extract " ++ 
      Printer.pr_constructor env c ++ 
      str " at " ++
      int i ++ 
      str " then (" ++
      nested_extraction_str ++
      str ")"
    )
  )

type composition = 
  (* ((the function getting applied, how to extract it), (argument to compose, how to extract it) list) *)
  | Composition of ((EConstr.t * composition) * (EConstr.t * composition) array)
  (* (what is getting extracted, Type of what is getting extracted, index from which it is getting extracted, how is it getting extracted)*)
  | FromIndex of (EConstr.t * EConstr.types * int * extraction)
  (* The term is known from the environment so it doesn't have to be extracted *)
  | InEnv of EConstr.t

let rec composition_to_pp env sigma composition : Pp.t= 
  let print t = Printer.pr_econstr_env env sigma t in
  match composition with 
  | Composition ((f,f_composition), arg_compositions)->(
    let f_composition_pp = composition_to_pp env sigma f_composition in 
    let arg_pps = Array.map (fun (arg, arg_composition) ->(
      let arg_composition_pp = composition_to_pp env sigma arg_composition in 
      Pp.(
        str "(" ++ 
        print arg ++
        str ", " ++
        arg_composition_pp ++
        str "),")
    )) arg_compositions in
    Pp.(
      str "(" ++
      f_composition_pp ++
      str "(" ++
      seq (Array.to_list arg_pps) ++ 
      str "))"
    )
  )
  | FromIndex (t,t_type,i,extraction)-> Pp.(
    print t ++ str ":" ++ print t_type ++ 
    str " at " ++ int i ++ str " (" ++
    extraction_to_pp env sigma extraction ++ str ")"
  )
  | InEnv _ -> Pp.(str "InEnv")

let rec find_composition env sigma indices_to_compose_from term_to_compose : composition option =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "find composition for: " ++ 
    print term_to_compose ++ 
    str " from " ++ 
    seq (List.map (fun x -> print x ++ str ", ") (Array.to_list indices_to_compose_from)) 
  );
  match EConstr.kind sigma term_to_compose with
  | Var _ | Const _ | Ind _ | Construct _ -> Some (InEnv term_to_compose)
  | _ ->(
    let composition_result = find_arg env sigma term_to_compose indices_to_compose_from in 
    match composition_result with
    | Some (i, extraction) ->
      ( Feedback.msg_debug Pp.(str "found extraction in index " ++ int i); 
      Some (FromIndex (term_to_compose, snd (Typing.type_of env sigma term_to_compose),  i, extraction)))
    | None -> (
      match  EConstr.kind sigma term_to_compose with
      | App (f,args) -> (
        Feedback.msg_debug Pp.(str "try to compose " ++ print term_to_compose);
        Option.bind 
        (find_composition env sigma indices_to_compose_from f)
        (fun f_composition -> 
          Option.map 
            (fun args_composition -> (Composition ((f, f_composition), args_composition))) 
            (array_map_option 
              (fun e -> Option.map (fun arg_composition -> (e, arg_composition)) (find_composition env sigma indices_to_compose_from e)) 
              args
            )
        )
      )
      | _ -> None
    )
  )
and find_extraction env sigma term_to_extract term_to_extract_from : extraction option =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "find_extraction for " ++ 
    print term_to_extract ++ 
    str " from " ++ 
    print term_to_extract_from
  );
  if EConstr.eq_constr_nounivs sigma term_to_extract term_to_extract_from 
  then Some Id 
  else
    match EConstr.kind sigma term_to_extract_from with
      | App (f, args) -> (
          match EConstr.kind sigma f with
          | Construct c -> (
              let first_arg_option =
                find_arg env sigma term_to_extract args
              in
              match first_arg_option with
              | Some (i, result) -> Some (Extraction (c, i, result))
              | None -> None
          )
          | _ -> None
      )
      | _ -> None
and find_arg env sigma term_to_extract args : (int * extraction) option =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "find_arg for " ++ 
    print term_to_extract ++ 
    str " from " ++ 
    seq (List.map (fun e -> Pp.(print e ++ str ", ")) (Array.to_list args)) 
  );
  Seq.find_map
  (fun (i, x) ->
    Option.map
      (fun r -> (i,r))
      (find_extraction env sigma term_to_extract x)
  )
  (Array.to_seqi args)

type projectable_result =
  | Simple
  | Dependent of composition
  | NotProjectable
  | Error

let is_projectable env sigma (cstr:Constr.pconstructor) i : projectable_result =
  let open Pp in
  let (c,u) = cstr in
  Feedback.msg_debug
    (str "projectability test of " ++ Printer.pr_constructor env c ++ str " on index " ++ Pp.int i);
    if i >= 0 && i < Inductiveops.constructor_nallargs env c then (
      (* let sigma, constructor_type = Typing.type_of env sigma term in *)
      let constructor_type =
        Inductiveops.e_type_of_constructor env sigma (c, EConstr.EInstance.make u)
      in
      let field_env, field_type, field_target =
        get_ith_field_type env constructor_type i
      in
      let target_env, target_type, lifted_field_type =
        constructor_target field_env field_target field_type
      in
      let target_sigma = Evd.from_env target_env in
      Feedback.msg_debug
        (str "projecting type "
        ++ Printer.pr_econstr_env target_env target_sigma lifted_field_type
        ++ str " from "
        ++ Printer.pr_econstr_env target_env target_sigma target_type);
      let field_sigma = Evd.from_env field_env in
      if is_dependent field_sigma field_type i then(
        Feedback.msg_debug (Pp.str "Dependent");
        match EConstr.kind sigma target_type with 
        | App (_, args) -> (
          Feedback.msg_debug (Pp.str "Searching for composition");
          match find_composition target_env target_sigma args lifted_field_type with
          | Some r -> Dependent r
          | None -> NotProjectable
          )
          | _ -> NotProjectable
      )
      else Simple)
    else (
      Feedback.msg_debug (Pp.str "Index out of bounce");
      Error)


let is_projectable_econstr env sigma term i : projectable_result =
  let open Pp in
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug
    (str "projectability test of " ++ print term ++ str " on index " ++ Pp.int i);
  match EConstr.kind sigma term with
  | Construct (c,u) ->
      is_projectable env sigma (c, EConstr.EInstance.kind sigma u) i
  | _ ->
      Feedback.msg_debug (Pp.str "Term is not a Constructor");
      Error

(* builds the nested match statement to follow the indices of the extractrion and returning type_to_extract->type_to_extract *)
let rec build_extraction env sigma type_to_extract term term_type extraction_result =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "build extraction: extract " ++
    print type_to_extract ++
    str "\nfrom\n" ++
    print term ++ str ":" ++ print term_type ++
    str "\nwith\n" ++
    extraction_to_pp env sigma extraction_result
  );
  match extraction_result with
  | Id -> EConstr.mkLambda (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, type_to_extract, EConstr.Vars.lift 1 term)
  | Extraction (((_, pos), _) as c, i, next_extraction_result) -> (
    let nargs = Inductiveops.constructor_nrealargs env (fst  c) in 
    let next_term =  EConstr.mkRel (nargs - i) in 
    let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
    let (_, next_term_type, _) = get_ith_field_type env constructor_type i in
    let default = EConstr.mkLambda (annot_of_string_numbered "t" None EConstr.ERelevance.relevant, type_to_extract, EConstr.mkRel 1) in 
    let special = build_extraction env sigma type_to_extract next_term next_term_type next_extraction_result in
    Combinators.make_selector env sigma ~pos ~special ~default term term_type
  )

let get_index_list_annots env sigma inductive_type_term =
  let rec helper term i l = 
    match EConstr.kind sigma term with
    | Prod (name,ty,rest) ->(
      let annot = ((annot_of_string_numbered "i" (Some i) EConstr.ERelevance.relevant),ty) in 
      helper rest (i+1) (annot::l)
    )
    | _ -> (l,i)
  in 
    helper  inductive_type_term 0 []

let get_default_list_annots env sigma composition_result = 
  let rec helper composition_result i l =
    match composition_result with
    | InEnv _ -> (l,i)
    | Composition ((f,f_composition), args_compositions) ->(
        let (f_list,i) = helper f_composition i l in 
        Array.fold_left
        (fun (l,i) (_,arg_composition) -> helper arg_composition i l)
        (f_list,i)
        (args_compositions)
    )
    | FromIndex (_, term_type, _, _) -> ((annot_of_string_numbered "d" (Some i) EConstr.ERelevance.relevant, term_type)::l, i+1)
  in
    helper composition_result 0 []

let rec get_extracted_term env sigma term extraction =
  match extraction with 
    (* The end of extraction is reached *)
    | Id -> term
    (* (constructor from to extract with universe, arg index to extract, nested further extraction) *)
    | Extraction (_, i, extraction) -> 
      let (_, args) = EConstr.decompose_app sigma term in
      get_extracted_term env sigma args.(i) extraction


let rec get_defaults_from_args env sigma args composition_result =
  match composition_result with
    | Composition ((_, f_composition), arg_compositions) ->(
      let f_defaults = get_defaults_from_args env sigma args f_composition in 
      let arg_defaults =  List.concat_map (fun (_, composition) -> get_defaults_from_args env sigma args composition) (Array.to_list arg_compositions) in 
      List.append f_defaults arg_defaults 
    )
    | FromIndex (_, _, i, extraction) -> [get_extracted_term env sigma args.(i) extraction]
    | InEnv e -> [e]

(* match term and return i'th (0 based) field of constructor c*)
let build_simple_projection env sigma e_type (((ind,pos) as cosntr,u) as c) i =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "build simple projection for " ++ 
    Printer.pr_constructor env cosntr ++ 
    str " at " ++ int i);
  let c_nargs = Inductiveops.constructor_nrealargs env (fst  c) in 
  let c_type = Inductiveops.e_type_of_constructor env sigma c in
  let (_, next_term_type, _) = get_ith_field_type env c_type i in
  let type_of_inductive = Inductiveops.type_of_inductive env (ind,u) in 
  let (index_annots_list, n_index_annots) = get_index_list_annots env sigma type_of_inductive in
  Feedback.msg_debug Pp.(str "INDICES:" ++ seq (List.map (fun (annot, ty) -> Names.Name.print (Context.binder_name annot) ++ str ":" ++ print ty ++ str ",") index_annots_list) );
  let special = EConstr.mkLambda (Context.make_annot Names.Anonymous EConstr.ERelevance.relevant, next_term_type, EConstr.mkRel (c_nargs - i + 1)) in 
  let default = EConstr.mkLambda (annot_of_string_numbered "t" None EConstr.ERelevance.relevant, next_term_type, EConstr.mkRel 1) in 
  let match_term_env = push_e_rel_assums (List.rev index_annots_list) env in
  let match_term_sigma = Evd.from_env match_term_env in 
  let match_term = Combinators.make_selector match_term_env match_term_sigma ~pos ~special ~default (EConstr.mkRel 1) e_type in 
  Feedback.msg_debug Pp.(str "match term:\n" ++ print match_term); 
  let projection_term = pack_lambda index_annots_list (pack_lambda [(annot_of_string_numbered "e" None EConstr.ERelevance.relevant, e_type)] match_term) in 
  Feedback.msg_debug Pp.(str "projection term:\n" ++ print projection_term); 
  projection_term


let build_dependent_projection_type env sigma composition_result default_annots_list n_default_annots index_annots_list n_index_annots =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "build dependent projection type for composition:\n" ++
    composition_to_pp env sigma composition_result ++
    str "\nwith indices\n" ++ 
    seq (List.map (fun (annot, ty) -> Names.Name.print (Context.binder_name annot) ++ str ":" ++ print ty ++ str ",") index_annots_list) ++ 
    str "\nwith default\n" ++ 
    seq (List.map (fun (annot, ty) -> Names.Name.print (Context.binder_name annot) ++ str ":" ++ print ty ++ str ",") default_annots_list)  
  );
  let rec helper composition_result nth_extraction =
  match composition_result with 
  | Composition ((f,f_composition), args_compositions) ->(
    let (nth_extraction, f_extraction) = helper f_composition nth_extraction in 
    let (nth_extraction, args_extractions) = Array.fold_left_map (fun nth_extraction arg_composition ->(
      helper (snd arg_composition) nth_extraction
    )) nth_extraction args_compositions in 
    (nth_extraction, EConstr.mkApp (f_extraction, args_extractions))
  )
  | FromIndex (t,type_to_extract,i,extraction) ->(
    let term_index = n_index_annots + n_default_annots + 1 - i in
    let (_,term_type) = List.nth index_annots_list (i) in 
    let extraction_term = build_extraction env sigma type_to_extract (EConstr.mkRel term_index) term_type extraction in 
    (nth_extraction+1, EConstr.mkApp (extraction_term, [|EConstr.mkRel (n_default_annots - nth_extraction)|]))
  )
  | InEnv t -> (nth_extraction, t)
  in 
    snd (helper composition_result 0)

let pack_rel_args_array n =
  Array.init n (fun i -> EConstr.mkRel (n-i)) 

let make_case_with_branch_map env sigma e ctype p branch_map = 
  let IndType(indf,_) as indt =
    try Inductiveops.find_rectype env sigma ctype
    with Not_found ->
      CErrors.user_err
        Pp.(str "Cannot discriminate on inductive constructors with \
                  dependent types.") in
  let (ind, _),_ = Inductiveops.dest_ind_family indf in
  let () = Tacred.check_privacy env ind in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let cstrs = Inductiveops.get_constructors env indf in
  let brl =
    List.map (branch_map cstrs) (CList.interval 1 (Array.length mip.mind_consnames)) in
  let rci = EConstr.ERelevance.relevant in
  let ci = Inductiveops.make_case_info env ind RegularStyle in
  let deparsign = Inductiveops.make_arity_signature env sigma true indf in
  let p = EConstr.it_mkLambda_or_LetIn p deparsign in
  Feedback.msg_debug Pp.(str "now make_case_or_project");
  Inductiveops.make_case_or_project env sigma indt ci (p, rci) e (Array.of_list brl)



let build_dependent_projection env sigma c i composition_result =
  let ((ind,pos),u) = c in 
  let type_of_inductive = Inductiveops.type_of_inductive env (ind,u) in 
  let (index_annots_list, n_index_annots) = get_index_list_annots env sigma type_of_inductive in
  let e_type = EConstr.mkApp (EConstr.mkIndU (ind,u), (pack_rel_args_array n_index_annots)) in 
  let env_inner = push_e_rel_assums (List.rev index_annots_list) env in 
  let env_inner = push_e_rel_assums [(annot_of_string_numbered "e" None EConstr.ERelevance.relevant, e_type)] env_inner in
  let sigma_inner = Evd.from_env env_inner in
  let print t = Printer.pr_econstr_env env_inner sigma_inner t in
  let IndType(ind_fam,_) = Inductiveops.find_rectype env_inner sigma_inner e_type in
  let cst_sums = Inductiveops.get_constructors env_inner ind_fam in
  Feedback.msg_debug Pp.(str "e_type: " ++ print e_type);
  let (default_annots_list, n_default_annots) = get_default_list_annots env_inner sigma composition_result in
  let env_inner = push_e_rel_assums (List.rev default_annots_list) env_inner in
  let sigma_inner = Evd.from_env env_inner in
  let type_annotation_template = build_dependent_projection_type env_inner sigma_inner composition_result default_annots_list n_default_annots index_annots_list n_index_annots in 
  let print t = Printer.pr_econstr_env env_inner sigma_inner t in
  Feedback.msg_debug Pp.(str "PROJECTION_TYPE:\n" ++ print type_annotation_template);
  let nargs = Inductiveops.constructor_nrealargs env_inner (fst  c) in 
  (*+1 because it is under a function*)
  let match_indices (cst_sum:Inductiveops.constructor_summary) type_annot_template =(
    let cst_type = Inductiveops.type_of_constructor env cst_sum.cs_cstr in
    let (_,concl_type,_) = constructor_target env cst_type (EConstr.mkRel 1) in
    let (_,args) = EConstr.decompose_app sigma_inner concl_type in
    let type_annot = EConstr.Vars.lift cst_sum.cs_nargs type_annot_template in
    let rec helper i j n return_type = 
      if j <= n then return_type
      else(
          helper (i+1) (j-1) n (Termops.replace_term sigma_inner (EConstr.mkRel (j+cst_sum.cs_nargs)) args.(i) return_type)
        ) 
    in 
    helper 0 (n_index_annots+n_default_annots+1) (n_default_annots+1) type_annot
  )
  in
  let special_index = (nargs - i + 1) in 
  let special_type = match_indices cst_sums.(pos-1) type_annotation_template in
  let print t = Printer.pr_econstr_env env_inner sigma_inner t in
  Feedback.msg_debug Pp.(str "SPECIAL_TYPE:\n" ++ print special_type);
  let e_index = n_default_annots + 1 in
  let make_return_type type_annotation_template = (
    let return_type = EConstr.Vars.lift (n_index_annots+1) type_annotation_template in
    let rec helper i j n return_type = 
      if j <= n then return_type
      else(
          helper (i-1) (j-1) n (Termops.replace_term sigma_inner (EConstr.mkRel (j+n_index_annots+1)) (EConstr.mkRel i) return_type)
        ) 
    in 
    let return_type = helper (n_index_annots+1) (n_index_annots+n_default_annots+1) (n_default_annots+1) return_type in
    EConstr.mkProd (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, return_type, EConstr.Vars.lift 1 return_type)
  ) in
  let e_match = make_case_with_branch_map env_inner sigma_inner (EConstr.mkRel e_index) e_type (make_return_type type_annotation_template)
    (fun cst_sums  i -> 
      if i == pos then 
        let x = (EConstr.it_mkLambda_or_LetIn (EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, special_type, EConstr.mkRel special_index)) cst_sums.(i-1).cs_args) in 
      Feedback.msg_debug Pp.(str "constr: " ++ int i ++ str ": " ++ print x);
      x
    else 
      (
        let defaulttype = match_indices cst_sums.(i-1) type_annotation_template in 
        let x =(EConstr.it_mkLambda_or_LetIn (EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, defaulttype, EConstr.mkRel 1)) cst_sums.(i-1).cs_args) in
        Feedback.msg_debug Pp.(str "constr: " ++ int i ++ str ": " ++ print x);
        x
      )
    )       
  in 
  Feedback.msg_debug Pp.(str "E_MATCH: " ++ print e_match);
  let (sigma_inner, type_of_e_match) = Typing.type_of env_inner sigma_inner e_match in
  let print t = Printer.pr_econstr_env env_inner sigma_inner t in
  Feedback.msg_debug Pp.(str "TYPE_OF:\n" ++ print type_of_e_match);
  pack_lambda ((annot_of_string_numbered "e" None EConstr.ERelevance.relevant, e_type)::index_annots_list) (pack_lambda default_annots_list e_match)


let build_projection env sigma constructor_term i =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "build projection for " ++
    print constructor_term ++
    str " at index " ++
    int i
    );
    match EConstr.kind sigma constructor_term with
    | Construct (((ind,pos),u) as c) ->(
      let type_of_inductive = Inductiveops.type_of_inductive env (ind,u) in 
      let (index_annots_list, n_index_annots) = get_index_list_annots env sigma type_of_inductive in
      let e_type = EConstr.mkApp (EConstr.mkIndU (ind,u), (pack_rel_args_array n_index_annots)) in 
      match is_projectable_econstr env sigma constructor_term i with
      | Simple -> Some (build_simple_projection env sigma e_type c i)
      | Dependent composition_result -> (
          Some (build_dependent_projection env sigma c i composition_result)
      )
      | NotProjectable -> None
      | Error -> None
  )
  | _ -> None
  

let build_projection_command e i =
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "called build projection for: " ++
    print term ++
    str " on index " ++
    int i 
  ); 
  match build_projection env sigma term i with
  | Some proj -> (
    Feedback.msg_debug (Pp.str "Projection found:"); 
    Feedback.msg_debug (print proj);
    let (sigma, proj_type) = Typing.type_of env sigma proj in
    let print t = Printer.pr_econstr_env env sigma t in
    Feedback.msg_debug Pp.(
      str "Projection Type:\n" ++
      print proj_type
    )
    )
  | None -> Feedback.msg_debug (Pp.str "No Projection Found")

let is_projectable_command e i =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  match is_projectable_econstr env sigma term i with
  | Simple -> Feedback.msg_debug (Pp.str "Simple")
  | Dependent _ -> Feedback.msg_debug (Pp.str "Dependant")
  | NotProjectable -> Feedback.msg_debug (Pp.str "Not Projectable")
  | Error -> Feedback.msg_debug (Pp.str "Error")
