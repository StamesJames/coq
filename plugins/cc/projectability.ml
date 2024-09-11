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



type extraction = 
  (* The end of extraction is reached *)
  | Id 
  (* (constructor from to extract with universe, arg index to extract, nested further extraction) *)
  | Extraction of ((Names.constructor * EConstr.EInstance.t) * int * extraction)

type composition = 
  (* ((the function getting applied, how to extract it), (argument to compose, how to extract it) list) *)
  | Composition of ((EConstr.t * composition) * (EConstr.t * composition) array)
  (* (what is getting extracted, Type of what is getting extracted, index from which it is getting extracted, how is it getting extracted)*)
  | FromIndex of (EConstr.t * EConstr.types * int * extraction)
  (* The term is globaly accassable so it doesn't have to be extracted *)
  | Global

exception NOT_YET_IMPLEMENTED    

let rec find_composition env sigma indices_to_compose_from term_to_compose : composition option =
  let composition_result = find_arg env sigma term_to_compose indices_to_compose_from in 
  match composition_result with
  | Some (i, extraction) -> Some 
    (FromIndex (term_to_compose, snd (Typing.type_of env sigma term_to_compose),  i, extraction))
  | None -> (
    match  EConstr.kind sigma term_to_compose with
    | App (f,args) -> (
      try
        let f_composition = Option.get (find_composition env sigma indices_to_compose_from f) in 
        let args_compositions = Array.map (fun e -> (e, Option.get (find_composition env sigma indices_to_compose_from e))) args in 
        Some (Composition ((f, f_composition), args_compositions))
      with Invalid_argument _ -> None
    )
    | _ -> None
  )
and find_extraction env sigma term_to_extract_from term_to_extract : extraction option =
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
        if is_dependent field_sigma field_type i then
          match EConstr.kind sigma target_type with 
          | App (_, args) -> (
              match find_composition target_env target_sigma args lifted_field_type with
            | Some r -> Dependent r
            | None -> NotProjectable
          )
          | _ -> NotProjectable
        else Simple)
      else (
        Feedback.msg_debug (Pp.str "index out of bounce");
        Error)
  | _ ->
      Feedback.msg_debug (Pp.str "Term is not a Constructor");
      Error

(* builds the nested match statement to follow the indices of the extractrion and returning type_to_extract->type_to_extract *)
let rec build_extraction env sigma type_to_extract term term_type extraction_result =
  match extraction_result with
  | Id -> EConstr.mkLambda (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, type_to_extract, term)
  | Extraction (((_, pos), _) as c, i, next_extraction_result) -> (
    let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
    let next_term =  EConstr.mkRel (1 + nargs - i ) in 
    let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
    let (_, next_term_type, _) = get_ith_field_type env constructor_type i in
    let default = EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, type_to_extract, EConstr.mkRel 1) in 
    let special = build_extraction env sigma type_to_extract next_term next_term_type next_extraction_result in
    Combinators.make_selector env sigma ~pos ~special ~default term term_type
  )

let annot_of_string_numbered s i r = 
  Context.make_annot (Names.Name.mk_name (Nameops.make_ident s (i))) r

let rec push_ind_param_index_asums env sigma term i =
  match EConstr.kind sigma term with
  | Prod (name,ty,rest) ->(
    let new_env = (Termops.push_rel_assum ((annot_of_string_numbered "i" (Some i) EConstr.ERelevance.relevant),ty) env) in 
    push_ind_param_index_asums new_env sigma rest (i+1)
  )
  | t -> Termops.push_rel_assum ((annot_of_string_numbered "e" None EConstr.ERelevance.relevant),term) env

let rec push_extraction_defaults env sigma composition_result i = 
  match composition_result with
  | Global -> env
  | Composition ((f,f_composition), args_compositions) ->(
      let env = push_extraction_defaults env sigma f_composition i in 
      Seq.fold_left
      (fun env (j,(_,arg_composition)) -> push_extraction_defaults env sigma arg_composition (i+1+j))
      env
      (Array.to_seqi args_compositions)
  )
  | FromIndex (_, term_type, _, _) -> Termops.push_rel_assum ((annot_of_string_numbered "d" (Some i) EConstr.ERelevance.relevant), term_type) env 

let build_projection_env env sigma inductive composition_result = 
  let env = push_ind_param_index_asums env sigma (Inductiveops.type_of_inductive env inductive) 1 in 
  push_extraction_defaults env sigma composition_result 1

let build_simple_projection env sigma ((((_,pos),_) as c)) term i =
  let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
  let special  =  EConstr.mkRel (1 + nargs - i ) in 
  let (sigma, term_type) = Typing.type_of env sigma term in
  let constructor_type = Inductiveops.e_type_of_constructor env sigma c in
  let (_, next_term_type, _) = get_ith_field_type env constructor_type i in
  let default = EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, next_term_type, EConstr.mkRel 1) in 
  Combinators.make_selector env sigma ~pos ~special ~default term term_type

let rec build_dependent_projection_type env sigma composition_result nth_extraction =
  match composition_result with 
  | Composition ((f,f_composition), args_compositions) ->(
    let (nth_extraction, f_extraction) = build_dependent_projection_type env sigma f_composition nth_extraction in 
    let args_extractions_options = Array.make (Array.length args_compositions) None in 
    let nth_extraction = 
      fst @@ Array.fold_left
      (fun (nth_extraction, i) (arg,arg_composition) ->(
        let (nth_extraction, arg_extraction) = build_dependent_projection_type env sigma arg_composition nth_extraction in 
        args_extractions_options.(i) <- Some arg_extraction; 
        (nth_extraction, i+1)
      ))
      (nth_extraction, 0)
      args_compositions in
    let args_extractions = Array.map Option.get args_extractions_options in
    (nth_extraction, EConstr.mkApp (f_extraction, args_extractions))
  )
  | FromIndex (t,type_to_extract,i,extraction) ->(
    let (term_index,_,term_type) = Termops.lookup_rel_id (Nameops.make_ident "i" (Some i)) (Environ.rel_context env) in 
    let extraction_term = build_extraction env sigma type_to_extract (EConstr.mkRel term_index) (EConstr.of_constr term_type) extraction in 
    let (default_index,_,_) = Termops.lookup_rel_id (Nameops.make_ident "d" (Some nth_extraction)) (Environ.rel_context env) in 
    (nth_extraction+1, EConstr.mkApp (extraction_term, [|EConstr.mkRel default_index|]))
    
  )
  | Global -> raise NOT_YET_IMPLEMENTED

let build_projection env sigma term i = 
  match EConstr.kind sigma term with
  | Construct (((ind,pos),u) as c) ->(
    match is_projectable env sigma term i with
    | Simple -> Some (build_simple_projection env sigma c term i)
    | Dependent r ->(
      let env = build_projection_env env sigma (ind,u) r in
      let constroctor_type = Inductiveops.type_of_constructor env c in
      let (_,field_type,_) = get_ith_field_type env constroctor_type i in
      let projection_type = build_dependent_projection_type env sigma r 1 in 
      let default = EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, snd projection_type, EConstr.mkRel 1) in
      let nargs = Inductiveops.constructor_nallargs env (fst  c) in 
      let special_index  =  EConstr.mkRel (1 + nargs - i ) in 
      let special = EConstr.mkLambda (Context.make_annot (Names.Name.Anonymous) EConstr.ERelevance.relevant, snd projection_type, special_index) in
      let (e,_,e_type) = Termops.lookup_rel_id (Nameops.make_ident "e" None) (Environ.rel_context env) in 
      Some (Combinators.make_selector env sigma ~pos ~special ~default (EConstr.mkRel e) (EConstr.of_constr e_type))
    )
    | NotProjectable -> None
    | Error -> None
  )
  | _ -> None
  

let build_projection_command e i = 
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  match build_projection env sigma term i with
  | Some proj -> Feedback.msg_debug (Pp.str "Build")
  | None -> Feedback.msg_debug (Pp.str "Not Projectable")

let is_projectable_command e i =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  match is_projectable env sigma term i with
  | Simple -> Feedback.msg_debug (Pp.str "Simple")
  | Dependent _ -> Feedback.msg_debug (Pp.str "Dependant")
  | NotProjectable -> Feedback.msg_debug (Pp.str "Not Projectable")
  | Error -> Feedback.msg_debug (Pp.str "Error")
