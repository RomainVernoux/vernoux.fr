(** Tells if an operator is compatible with a SQL database. See specification 
    for a formal definition *)
val compatible_operator : Qir.operator -> bool
