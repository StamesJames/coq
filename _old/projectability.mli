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
(* The term is known from the environment so it doesn't have to be extracted *)
| InEnv of EConstr.t

type projectable_result =
  | Simple
  | Dependent of (Evd.evar_map * composition)
  | NotProjectable
  | Error
    

 val get_defaults_from_args :'a ->
    Evd.evar_map ->
    Evd.econstr array ->
    composition ->
    Evd.econstr list

val is_projectable : Environ.env ->
    Evd.evar_map ->
    Constr.pconstructor ->
    int ->
    projectable_result

val build_dependent_projection : Environ.env ->
  Evd.evar_map ->
  Names.constructor * EConstr.EInstance.t ->
  int ->
  composition ->
  Evd.econstr
