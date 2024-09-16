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

let is_projectable env sigma term i : projectable_result =
  let open Pp in
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug
    (str "projectability test of " ++ print term ++ str " on index " ++ Pp.int i);
  match EConstr.kind sigma term with
  | Construct (c, u) ->
      if i >= 0 && i < Inductiveops.constructor_nallargs env c then (
        (* let sigma, constructor_type = Typing.type_of env sigma term in *)
        let constructor_type =
          Inductiveops.e_type_of_constructor env sigma (c, u)
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
  | Id -> EConstr.mkLambda (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, type_to_extract, term)
  | Extraction (((_, pos), _) as c, i, next_extraction_result) -> (
    let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
    let next_term =  EConstr.mkRel (1 + nargs - i ) in 
    let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
    let (_, next_term_type, _) = get_ith_field_type env constructor_type i in
    let default = EConstr.mkLambda (annot_of_string_numbered "t" None EConstr.ERelevance.relevant, type_to_extract, EConstr.mkRel 1) in 
    let special = build_extraction env sigma type_to_extract next_term next_term_type next_extraction_result in
    Combinators.make_selector env sigma ~pos ~special ~default term term_type
  )



let get_index_list_annots env sigma term =
  let rec helper term i l = 
    match EConstr.kind sigma term with
    | Prod (name,ty,rest) ->(
      let annot = ((annot_of_string_numbered "i" (Some i) EConstr.ERelevance.relevant),ty) in 
      helper rest (i+1) (annot::l)
    )
    | t -> (((annot_of_string_numbered "e" None EConstr.ERelevance.relevant),term)::l,i+1)
  in 
    helper  term 0 []

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

(* match term and return i'th (0 based) field of constructor c*)
let build_simple_projection env sigma (((_,pos),_) as c) term i =
  let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
  let (sigma, term_type) = Typing.type_of env sigma term in
  let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
  let (_, next_term_type, _) = get_ith_field_type env constructor_type i in
  let special  =  EConstr.mkLambda (Context.make_annot Names.Anonymous EConstr.ERelevance.relevant, next_term_type, EConstr.mkRel (nargs - i )) in 
  let default = EConstr.mkLambda (annot_of_string_numbered "t" None EConstr.ERelevance.relevant, next_term_type, EConstr.mkRel 1) in 
  Combinators.make_selector env sigma ~pos ~special ~default term term_type

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
    let term_index = n_default_annots + n_index_annots - i in
    let (_,term_type) = List.nth index_annots_list (i+1 -1) in 
    let extraction_term = build_extraction env sigma type_to_extract (EConstr.mkRel term_index) term_type extraction in 
    (nth_extraction+1, EConstr.mkApp (extraction_term, [|EConstr.mkRel nth_extraction|]))
  )
  | InEnv t -> (nth_extraction, t)
  in 
    snd (helper composition_result 1)


let build_projection env sigma term i =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(
    str "build projection for " ++
    print term ++
    str " at index " ++
    int i
  ); 
  match EConstr.kind sigma term with
  | Construct (((ind,pos),u) as c) ->(
    match is_projectable env sigma term i with
    | Simple -> Some (build_simple_projection env sigma c term i)
    | Dependent composition_result ->(
      let type_of_inductive = Inductiveops.type_of_inductive env (ind,u) in 
      let (index_annots_list, n_index_annots) = get_index_list_annots env sigma type_of_inductive in
      let (default_annots_list, n_default_annots) = get_default_list_annots env sigma composition_result in
      let env_with_indices = push_e_rel_assums (List.rev index_annots_list) env in 
      let env_with_indices_and_defaults = push_e_rel_assums (List.rev default_annots_list) env_with_indices in
      let projection_type = build_dependent_projection_type env_with_indices_and_defaults sigma composition_result default_annots_list n_default_annots index_annots_list n_index_annots in 
      let default = EConstr.mkLambda (annot_of_string_numbered "t" None EConstr.ERelevance.relevant, projection_type, EConstr.mkRel 1) in
      let nargs = Inductiveops.constructor_nallargs env_with_indices_and_defaults (fst  c) in 
      let special_index  =  EConstr.mkRel (1 + nargs - i ) in 
      let special = EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, projection_type, special_index) in
      let e_index = n_default_annots + 1 in
      let (_,e_type) = List.nth index_annots_list 0 in
      let e_match = (Combinators.make_selector env_with_indices_and_defaults sigma ~pos ~special ~default (EConstr.mkRel e_index) e_type) in 
      let rec pack_prod l e = 
        match l with 
        | [] -> e 
        | (annot,ty)::xs -> pack_prod xs (EConstr.mkProd (annot, ty, e))
      in
      Some (pack_prod index_annots_list (pack_prod default_annots_list e_match))
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
  | Some proj -> (Feedback.msg_debug (Pp.str "Projection found:"); Feedback.msg_debug (print proj))
  | None -> Feedback.msg_debug (Pp.str "No Projection Found")

let is_projectable_command e i =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  match is_projectable env sigma term i with
  | Simple -> Feedback.msg_debug (Pp.str "Simple")
  | Dependent _ -> Feedback.msg_debug (Pp.str "Dependant")
  | NotProjectable -> Feedback.msg_debug (Pp.str "Not Projectable")
  | Error -> Feedback.msg_debug (Pp.str "Error")
