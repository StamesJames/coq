val build_projection :
  Environ.env ->
  Evd.evar_map ->
  'a ->
  Constr.pconstructor ->
  int ->
  int ->
  Evd.econstr ->
  'b ->
  'c ->
  'd ->
  Evd.econstr ->
  Evd.econstr ->
  Evd.econstr -> Evd.econstr -> Evd.econstr -> Evd.evar_map * Evd.econstr
