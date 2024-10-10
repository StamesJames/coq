let get_ith_arg sigma i term=  
  let (rels_to_arg,rest) = EConstr.decompose_prod_n sigma i term in 
  let (arg_name,arg_type,rest) = EConstr.destProd sigma rest in
  (rels_to_arg, (arg_name, arg_type), rest)

(* [array_map_option f arr] maps f to arr returns Some when all calls retunr Some and None otherwise*)
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


(* checkt wether term depents on the last i Rels *)
let rec is_dependent env sigma term i =
  if i <= 0 then false
  else if Termops.dependent sigma (EConstr.mkRel i) term then true
  else is_dependent env sigma term (i - 1)

(* makes a annot of name s with optional number i and relevance r*)
let make_annot_numbered s i r = 
  Context.make_annot (Names.Name.mk_name (Nameops.make_ident s i)) r

(* The type to express a type extraction *)
type extraction = 
  (* The end of extraction is reached *)
  | Id 
  (* (constructor from to extract with universe, arg index to extract, nested further extraction) *)
  | Extraction of ((Names.constructor * EConstr.EInstance.t) * int * extraction)
let rec print_extraction env sigma extraction = 
  match extraction with 
  | Id -> Pp.str "Id"
  | Extraction ((c,_), i , extraction) ->(
    let nested_extraction_str = print_extraction env sigma extraction in 
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

(* type to express a composition of a type to extract *)
type composition = 
  (* ((the function getting applied, how to extract it), (argument to compose, how to extract it) list) *)
  | Composition of ((EConstr.t * composition) * (EConstr.t * composition) array)
  (* (what is getting extracted, Type of what is getting extracted, index from which it is getting extracted, how is it getting extracted)*)
  | FromIndex of (EConstr.t * EConstr.types * int * extraction)
  (* The term is known from the environment so it doesn't have to be extracted *)
  | InEnv of EConstr.t
let rec print_composition env sigma composition : Pp.t= 
  let print t = Printer.pr_econstr_env env sigma t in
  match composition with 
  | Composition ((f,f_composition), arg_compositions)->(
    let f_composition_pp = print_composition env sigma f_composition in 
    let arg_pps = Array.map (fun (arg, arg_composition) ->(
      let arg_composition_pp = print_composition env sigma arg_composition in 
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
    print_extraction env sigma extraction ++ str ")"
  )
  | InEnv _ -> Pp.(str "InEnv")

(* finds the composition of the term [term_to_compose] from the indices [indices_to_compose_from] *)
let rec find_composition env sigma terms_to_compose_from term_to_compose : (Evd.evar_map * composition) option =
  match EConstr.kind sigma term_to_compose with
  (* globaly defined objects don't have to be extracted *)
  | Var _ | Const _ | Ind _ | Construct _ -> Some (sigma, InEnv term_to_compose)
  | _ -> (
    (* search for a term from with the whole term can be extracted *)
    let extractrion_arg_result = find_arg env sigma term_to_compose terms_to_compose_from in 
    match extractrion_arg_result with
    | Some (i, extraction) ->
      let (sigma, term_to_compose_type) = (Typing.type_of env sigma term_to_compose) in
      (* term_to_compose:term_to_compose_type can be extracted from index i via extractrion *)      
      Some (sigma, (FromIndex (term_to_compose, term_to_compose_type, i, extraction)))
    | None -> (
      (* if no direct extraction was found we test wether we can compose the term from its subexpressions (currently only applicative terms are supported) *)
      match  EConstr.kind sigma term_to_compose with
      | App (f,args) -> (
        let f_composition = find_composition env sigma terms_to_compose_from f in 
        match f_composition with
        | Some (sigma, f_composition) ->(
          let sigma_ref = ref sigma in
          let args_composition = 
            array_map_option 
              (fun e -> 
                Option.map 
                (fun (sigma, arg_composition) -> 
                  sigma_ref := sigma; 
                  (e, arg_composition)) 
                (find_composition env !sigma_ref terms_to_compose_from e)
              ) 
              args 
          in
          let sigma = !sigma_ref in
          match args_composition with 
          | Some args_composition -> 
            Some (sigma, Composition ((f, f_composition), args_composition))
          | None -> None
        )
        | _ -> None 
      )
      | _ -> None
    )
  )
and find_extraction env sigma term_to_extract term_to_extract_from : extraction option =
  (* When the terms are equal we found the term we want to extract*)
  if EConstr.eq_constr_nounivs sigma term_to_extract term_to_extract_from 
  then Some Id 
  else
    (* if the term_to_extract_from is a constroctor application, we can try to recursively extract the term from the constructor term *)
    match EConstr.kind sigma term_to_extract_from with
      | App (f, args) -> (
          match EConstr.kind sigma f with
          | Construct c -> (
              let first_arg_option =
                find_arg env sigma term_to_extract args
              in
              match first_arg_option with
              | Some (i, result) -> 
                (* we found a extraction for term by projecting the ith field from c and then extracting further with result *)
                Some (Extraction (c, i, result))
              | None -> None
          )
          | _ -> None
      )
      | _ -> None
and find_arg env sigma term_to_extract args : (int * extraction) option =
  (* finds the first arg from which the term can be extracted *)
  Seq.find_map
  (fun (i, x) ->
    Option.map
      (fun r -> (i,r))
      (find_extraction env sigma term_to_extract x)
  )
  (Array.to_seqi args)

type projectable_result =
  | Simple
  | Dependent of (Evd.evar_map * composition)
  | NotProjectable
  | Error

let is_projectable env sigma (((ind,pos) as c,u):Constr.pconstructor) i : projectable_result =
  (* i is the field index seen in realargs *)
  let ind_nparams = Inductiveops.inductive_nparams env ind in
    if i >= 0 && i < Inductiveops.constructor_nrealargs env c then (
      (* Constructor type with all params indices and arguments *)
      let constructor_type =
        Inductiveops.e_type_of_constructor env sigma (c, EConstr.EInstance.make u)
      in
      let (field_local_rels, (field_annot,field_type), field_rest) = get_ith_arg sigma (i+ind_nparams) constructor_type in
      let field_env = 
        EConstr.push_rel_context (List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) (field_local_rels)) env 
      in 
      let print t = Printer.pr_econstr_env field_env sigma t in
      Feedback.msg_debug Pp.(str "FIELD_TYPE:\n"++print field_type);
      let field_rest_env = 
        EConstr.push_rel (Context.Rel.Declaration.LocalAssum (field_annot,field_type)) field_env 
      in 
      let print t = Printer.pr_econstr_env field_rest_env sigma t in
      Feedback.msg_debug Pp.(str "FIELD_TARGET:\n"++print field_rest);
      let target_local_rels, target_type = EConstr.decompose_prod sigma field_rest in
      let target_env = 
        EConstr.push_rel_context (List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) target_local_rels) field_rest_env 
      in 
      let lifted_field_type = EConstr.Vars.lift (List.length target_local_rels+1) field_type in
      let print t = Printer.pr_econstr_env target_env sigma t in
      Feedback.msg_debug Pp.(str "TARGET_TYPE:\n"++print target_type);
      Feedback.msg_debug Pp.(str "LIFTED_FIELD_TYPE:\n"++print lifted_field_type);

      (* we don't want the inductive params to be seen as dependencies so we just check for the last i bindings *)
      if is_dependent field_env sigma field_type i then(
        match EConstr.kind sigma target_type with 
        | App (_, args) -> (
          match find_composition target_env sigma args lifted_field_type with
          | Some (sigma, r) -> Dependent (sigma, r)
          | None -> NotProjectable
        )
        | _ -> NotProjectable
      )
      else Simple)
    else Error


(* builds the nested match statement to follow the indices of the extractrion and returning type_to_extract->type_to_extract *)
let rec build_extraction env sigma type_to_extract term term_type extraction_result =
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(str "=============BUILD_EXTRACTION============");
  Feedback.msg_debug Pp.(str "TYPE_TO_EXTRACT:\n" ++ print type_to_extract);
  Feedback.msg_debug Pp.(str "TERM:\n" ++ print term);
  Feedback.msg_debug Pp.(str "TERM_TYPE:\n" ++ print term_type);
  Feedback.msg_debug Pp.(str "=========================");
  
  match extraction_result with
  | Id -> EConstr.mkLambda (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, type_to_extract, EConstr.Vars.lift 1 term)
  | Extraction (((ind, pos), _) as c, i, next_extraction_result) -> (
    Feedback.msg_debug Pp.(str "CNSTR: " ++ Printer.pr_constructor env (fst c) ++ str "\nAT INDEX: " ++ int i);
    let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
    Feedback.msg_debug Pp.(str "NARGS: " ++ int nargs);
    let next_term =  EConstr.mkRel (nargs - i) in 
    Feedback.msg_debug Pp.(str "NEXT_TERM: " ++ print next_term);
    let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
    Feedback.msg_debug Pp.(str "CONSTRUCTOR_TYPE: " ++ print constructor_type);
    let ind_nparams = Inductiveops.inductive_nparams env ind in
    Feedback.msg_debug Pp.(str "IND_NPARAMS: " ++ int ind_nparams);
    let (_,(_,next_term_type),_) = get_ith_arg sigma (i+ind_nparams) constructor_type in
    Feedback.msg_debug Pp.(str "NEXT_TERM_TYPE: " ++ print next_term_type);
    let default = EConstr.mkLambda (make_annot_numbered "t" None EConstr.ERelevance.relevant, type_to_extract, EConstr.mkRel 1) in 
    Feedback.msg_debug Pp.(str "DEFAULT: " ++ print default);
    Feedback.msg_debug Pp.(str "=============BUILD_EXTRACTION SPECIAL============");
    let special = build_extraction env sigma type_to_extract next_term next_term_type next_extraction_result in
    Feedback.msg_debug Pp.(str "--------------BUILD_EXTRACTION SPECIAL--------------");
    Feedback.msg_debug Pp.(str "SPECIAL: " ++ print special);
    Combinators.make_selector env sigma ~pos ~special ~default term term_type
  )

let get_defaults_rel_context env sigma composition_result : (EConstr.rel_context * int) = 
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
    | FromIndex (_, term_type, _, _) -> (Context.Rel.Declaration.LocalAssum (make_annot_numbered "d" (Some i) EConstr.ERelevance.relevant, term_type)::l, i+1)
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
    | InEnv e -> []


let build_dependent_projection_type env sigma composition_result default_annots_list n_default_annots (index_annots_list:EConstr.rel_context) n_index_annots =
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
    let term_type = Context.Rel.Declaration.get_type (List.nth index_annots_list (n_index_annots - i -1)) in
    let term = EConstr.mkRel term_index in
    let print t = Printer.pr_econstr_env env sigma t in
    Feedback.msg_debug Pp.(str "N_INDEX_ANNOTS: " ++ int n_index_annots);
    Feedback.msg_debug Pp.(str "N_DEFAULT_ANNOTS: " ++ int n_default_annots);
    Feedback.msg_debug Pp.(str "I: " ++ int i);
    Feedback.msg_debug Pp.(str "TERM: " ++ print term);
    Feedback.msg_debug Pp.(str "TERM_TYPE: " ++ print term_type);
    Feedback.msg_debug Pp.(str "NTH_EXTRACTION: " ++ int nth_extraction);
    Feedback.msg_debug Pp.(str "=============BUILD_EXTRACTION EXTRACTION TERM============");

    let extraction_term = build_extraction env sigma type_to_extract term term_type extraction in 
    Feedback.msg_debug Pp.(str "--------------BUILD_EXTRACTION EXTRACTION TERM--------------");

    (nth_extraction+1, EConstr.mkApp (extraction_term, [|EConstr.mkRel (n_default_annots - nth_extraction)|]))
  )
  | InEnv t -> (nth_extraction, t)
  in 
    snd (helper composition_result 0)

let pack_rel_args_array n =
  Array.init n (fun i -> EConstr.mkRel (n-i)) 

let get_match_return_rel_context env sigma ctype = 
  let IndType(indf,_) =
  try Inductiveops.find_rectype env sigma ctype
  with Not_found ->
    CErrors.user_err
      Pp.(str "Cannot discriminate on inductive constructors with \
                dependent types.") in
  let deparsign = Inductiveops.make_arity_signature env sigma true indf in
  deparsign


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
  Inductiveops.make_case_or_project env sigma indt ci (p, rci) e (Array.of_list brl)


let build_dependent_projection env sigma (((ind,pos),u) as c) i composition_result =
  Feedback.msg_debug Pp.(str "BUILD DEPENDENT PROJECTION:\n" ++ print_composition env sigma composition_result);
  let type_of_inductive = Inductiveops.type_of_inductive env (ind,u) in 
  let print t = Printer.pr_econstr_env env sigma t in 
  Feedback.msg_debug Pp.(str "TYPE_OF_INDUCTIVE:\n" ++ print type_of_inductive);
  let (ind_allargs,_) = (EConstr.decompose_prod sigma type_of_inductive) in 
  let ind_allargs = List.map (fun (x,y) -> Context.Rel.Declaration.LocalAssum (x,y)) ind_allargs in
  let ind_nallargs = List.length ind_allargs in
  let e_type = EConstr.mkApp (EConstr.mkIndU (ind,u), (pack_rel_args_array ind_nallargs)) in 
  (* constructiong the first arguments for the projection to define the type of e *)
  let env_inner = EConstr.push_rel_context (Context.Rel.Declaration.LocalAssum (make_annot_numbered "e" None EConstr.ERelevance.relevant, e_type)::ind_allargs) env in 
  let IndType(ind_fam,_) = Inductiveops.find_rectype env_inner sigma e_type in
  let cst_sums = Inductiveops.get_constructors env_inner ind_fam in
  (* constructing the default valu_annots for the type extraction *)
  let (defaults_rel_context, n_default_annots) = get_defaults_rel_context env_inner sigma composition_result in
  let env_inner = EConstr.push_rel_context defaults_rel_context env_inner in
  Feedback.msg_debug Pp.(str "BUILD");
  let type_annotation_template = build_dependent_projection_type env_inner sigma composition_result defaults_rel_context n_default_annots ind_allargs ind_nallargs in
  let print t = Printer.pr_econstr_env env_inner sigma t in 
  Feedback.msg_debug Pp.(str "TYPE_ANNOTATION_TEMPLATE:\n" ++ print type_annotation_template);
  Feedback.msg_debug Pp.(str "BUILD DONE");
  (*let cnallargs = Inductiveops.constructor_nallargs env_inner (fst  c) in *)
  let cnrealargs = Inductiveops.constructor_nrealargs env_inner (fst  c) in 
  (*+1 because it is under a function*)
  let match_indices (cst_sum:Inductiveops.constructor_summary) type_annot_template =(
    Feedback.msg_debug Pp.(str "!!!!!!!!!!!!!!!!!!!!!!!\n" ++ Printer.pr_constructor env (fst cst_sum.cs_cstr) ++ str "\nnargs: " ++ int cst_sum.cs_nargs
    ++ str "!!!!!!!!!!!!!!!!!!!!!!!!");
    let cst_type = Inductiveops.type_of_constructor env cst_sum.cs_cstr in
    let concl_type = snd (EConstr.decompose_prod sigma cst_type) in
    let (_,args) = EConstr.decompose_app sigma concl_type in
    let type_annot = EConstr.Vars.lift cst_sum.cs_nargs type_annot_template in
    let rec helper i j n return_type = 
      if j <= n then return_type
      else(
          helper (i+1) (j-1) n (Termops.replace_term sigma (EConstr.mkRel (j+cst_sum.cs_nargs)) args.(i) return_type)
        ) 
    in 
    helper 0 (ind_nallargs+n_default_annots+1) (n_default_annots+1) type_annot
  )
  in
  (*+1 beacause it is later under a function*)
  let special_index = (cnrealargs - i +1) in 
  let special_type = match_indices cst_sums.(pos-1) type_annotation_template in
  let e_index = n_default_annots + 1 in
  let make_return_type type_annotation_template = (
    (* lift the while term over the match as in bindings*)
    let return_rel_context = get_match_return_rel_context env sigma e_type in
    let n_return_rel_context = List.length return_rel_context in
    Feedback.msg_debug Pp.(str "N_RETURN_REL_CONTEXT:\n" ++ int n_return_rel_context);
    let return_type = EConstr.Vars.lift n_return_rel_context type_annotation_template in
    (* replace the indices of the outer index terms with the inner bindings in the match as in  *)
    
    let rec helper i return_type = 
      if i >= n_return_rel_context then return_type else 
        helper (i+1) (Termops.replace_term sigma (EConstr.mkRel (n_return_rel_context+n_default_annots+1+ind_nallargs-i)) (EConstr.mkRel (ind_nallargs+1(*because e is binded another time*)-i)) return_type)
    in 
    let return_type = helper (Inductiveops.inductive_nparams env ind +1) return_type in
    
    EConstr.mkProd (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, return_type, EConstr.Vars.lift 1 return_type)
  ) in
  Feedback.msg_debug Pp.(str "RETRUN_TYPE:\n" ++ print (make_return_type type_annotation_template));
  let e_match = make_case_with_branch_map env_inner sigma (EConstr.mkRel e_index) e_type (make_return_type type_annotation_template)
    (fun cst_sums  i -> 
      if i == pos then 
        let x = (EConstr.it_mkLambda_or_LetIn (EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, special_type, EConstr.mkRel special_index)) cst_sums.(i-1).cs_args) in 
      x
    else 
      (
        let defaulttype = match_indices cst_sums.(i-1) type_annotation_template in 
        let x =(EConstr.it_mkLambda_or_LetIn (EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, defaulttype, EConstr.mkRel 1)) cst_sums.(i-1).cs_args) in
        x
      )
    )       
  in 
  let result = EConstr.it_mkLambda_or_LetIn (EConstr.it_mkLambda_or_LetIn e_match defaults_rel_context) (Context.Rel.Declaration.LocalAssum (make_annot_numbered "e" None EConstr.ERelevance.relevant, e_type)::ind_allargs) in 
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug Pp.(str "++++++++++++++++++++++++++++++++++++++++++++++++++++");
  Feedback.msg_debug Pp.(str "result");
  Feedback.msg_debug (print result );
  Feedback.msg_debug Pp.(str "++++++++++++++++++++++++++++++++++++++++++++++++++++");
  (*
  let (sigma, type_of_result) = Typing.type_of env sigma result in
  Feedback.msg_debug (print type_of_result );
  *)
  Feedback.msg_debug Pp.(str "++++++++++++++++++++++++++++++++++++++++++++++++++++");
  result


