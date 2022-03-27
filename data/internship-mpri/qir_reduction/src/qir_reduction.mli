exception Reduction_error of string


(** Reduces a term greedily (lists all redexes and contracts the first one
    until no redex remains). This method might not terminate for non strongly-
    normalizing terms *)
val greedy_reduce : Qir.expression -> Qir.expression


(** Considers all the ways to reduce a term and keeps one that has minimal
    measure (cf. specification) *)
val exhaustive_reduce : Qir.expression -> Qir.expression


(** Uses an heuristic to find a reduced form of the input expression that has
    a small measure. The number of reduction steps is bounded by an integer
    constant (cf. specification) *)
val heuristic_reduce : Qir.expression -> int -> Qir.expression
