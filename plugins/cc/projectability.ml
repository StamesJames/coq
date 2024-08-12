let rec get_target_type sigma term context =
  match EConstr.kind sigma term with 
  | Prod (name, _, target_type) -> get_target_type sigma target_type ()
  | t -> (context, term)

let rec get_ith_field_type sigma term i =
  match EConstr.kind sigma term with
  | Prod (name, field_type, target_type) -> 
    if i == 0 then 
      field_type
    else 
      get_ith_field_type sigma target_type (i-1)
  | _ -> raise Not_found

let is_projectable env sigma term i : bool =
  let term_kind = EConstr.kind sigma term in
  match term_kind with 
  | Construct (c, _) ->
      if i >= 0 && i < Inductiveops.constructor_nallargs env c then 
        let (sigma, constructor_type) = Typing.type_of env sigma term in
        let field_type = get_ith_field_type sigma constructor_type i in
        let (context, target_type) = get_target_type sigma constructor_type Context.Rel.empty in
        (match EConstr.kind sigma field_type with 
        | App (f, args) -> (
          match EConstr.kind sigma target_type with
          | App(f', args') -> 
            if Evarutil.eq_constr_univs_test ~evd:sigma ~extended_evd:sigma args'.(0) f then 
              Feedback.msg_debug (Pp.str "gleich 1") 
            else 
              Feedback.msg_debug (Pp.str "anders 1");
            if Evarutil.eq_constr_univs_test ~evd:sigma ~extended_evd:sigma args.(0) args'.(1) then
              Feedback.msg_debug (Pp.str "gleich 2") 
            else 
              Feedback.msg_debug (Pp.str "anders 2");
          | _ -> Feedback.msg_debug (Pp.str "target no App")
        )
        | _ -> Feedback.msg_debug (Pp.str "field no App"));
        Feedback.msg_debug (Printer.pr_econstr_env env sigma constructor_type);
        Feedback.msg_debug (Printer.pr_econstr_env env sigma field_type);
        Feedback.msg_debug (Printer.pr_econstr_env env sigma target_type);
        Feedback.msg_debug(Pp.str "passt sho");
        false
      else 
        (Feedback.msg_debug(Pp.str "index out of bounce");
        false)
  | _ -> 
    Feedback.msg_debug(Pp.str "Term is not a Constructor");
    false

let is_projectable_command e i = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, term) = Constrintern.interp_constr_evars env sigma e in
  if is_projectable env sigma term i then
    Feedback.msg_debug(Pp.str "projectable")
  else
    Feedback.msg_debug(Pp.str "NOT projectable")