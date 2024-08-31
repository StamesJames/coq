let rec get_target_type env term field_to_lift =
  let sigma = Evd.from_env env in
  match EConstr.kind sigma term with
  | Prod (name, ty, target_type) ->
      get_target_type
        (Termops.push_rel_assum (name, ty) env)
        target_type
        (EConstr.Vars.lift 1 field_to_lift)
  | t -> (env, term, field_to_lift)

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

type extraction_result =
  | NotExtractable
  | Id
  | Projection of Names.constructor * int * extraction_result
  | Composition of (EConstr.t * extraction_result) list
  | Index of int * extraction_result

let rec find_arg env sigma term_to_extract args is_top_level =
  Seq.find_map
    (fun (i, x) ->
      let result = is_extractable env sigma term_to_extract x is_top_level in
      match result with NotExtractable -> None | _ -> Some (i, result))
    (Array.to_seqi args)

and find_composition env sigma term_to_extract_from is_top_level term_to_extract
    =
  EConstr.fold sigma
    (fun acc t ->
      match acc with
      | Composition l -> (
          let new_result =
            is_extractable env sigma t term_to_extract_from is_top_level
          in
          match new_result with
          | NotExtractable -> NotExtractable
          | r -> Composition ((t, r) :: l))
      | _ -> NotExtractable)
    (Composition []) term_to_extract

and is_extractable env sigma term_to_extract term_to_extract_from is_top_level :
    extraction_result =
  let open Pp in
  let print t = Printer.pr_econstr_env env sigma t in
  Feedback.msg_debug
    (str "extraction test " ++ print term_to_extract ++ str " from "
   ++ print term_to_extract_from);
  if EConstr.eq_constr_nounivs sigma term_to_extract term_to_extract_from then (
    Feedback.msg_debug (str "is Id");
    Id)
  else (
    Feedback.msg_debug (str "not eq");
    match EConstr.kind sigma term_to_extract_from with
    | App (f, args) -> (
        match EConstr.kind sigma f with
        | Construct (c, _) -> (
            Feedback.msg_debug (str "Construct");
            let first_arg_option =
              find_arg env sigma term_to_extract args false
            in
            match first_arg_option with
            | Some (i, result) -> Projection (c, i, result)
            | None ->
                find_composition env sigma term_to_extract_from false
                  term_to_extract)
        | Ind _ when is_top_level -> (
            Feedback.msg_debug (str "Ind");
            let first_arg_option =
              find_arg env sigma term_to_extract args true
            in
            match first_arg_option with
            | Some (i, result) -> Index (i, result)
            | None ->
                find_composition env sigma term_to_extract_from true
                  term_to_extract)
        | _ ->
            Feedback.msg_debug (str "no Constructor");
            NotExtractable)
    | _ ->
        Feedback.msg_debug (str "no App");
        NotExtractable)

type projectable_result =
  | Simple
  | Dependent of extraction_result
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
          get_target_type field_env field_target field_type
        in
        let target_sigma = Evd.from_env target_env in
        Feedback.msg_debug
          (str "projecting type "
          ++ Printer.pr_econstr_env target_env target_sigma lifted_field_type
          ++ str " from "
          ++ Printer.pr_econstr_env target_env target_sigma target_type);
        let field_sigma = Evd.from_env field_env in
        if is_dependent field_sigma field_type i then
          match
            is_extractable target_env target_sigma lifted_field_type target_type
              true
          with
          | NotExtractable -> NotProjectable
          | r -> Dependent r
        else Simple)
      else (
        Feedback.msg_debug (Pp.str "index out of bounce");
        Error)
  | _ ->
      Feedback.msg_debug (Pp.str "Term is not a Constructor");
      Error

let is_projectable_command e i =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, term = Constrintern.interp_constr_evars env sigma e in
  match is_projectable env sigma term i with
  | Simple -> Feedback.msg_debug (Pp.str "Simple")
  | Dependent _ -> Feedback.msg_debug (Pp.str "Dependant")
  | NotProjectable -> Feedback.msg_debug (Pp.str "Not Projectable")
  | Error -> Feedback.msg_debug (Pp.str "Error")
