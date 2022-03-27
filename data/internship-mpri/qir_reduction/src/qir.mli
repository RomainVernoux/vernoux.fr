type value =
  (* | Null  // Not used for now *)
  | Number of int
  | String of string
  | Bool of bool

(* Built-in functions. Operations on values and aggregation functions. *)
type fun_builtin =
  | Add of expression * expression
  | Sub of expression * expression
  | Mul of expression * expression
  | Div of expression * expression
  | Lt of expression * expression
  | Lte of expression * expression
  | And of expression * expression
  | Or of expression * expression
  | Eq of expression * expression
  | Ite of expression * expression * expression
  | Avg of expression
  | Sum of expression

(* Operators. By convention, the first arguments represent the configuration
   and the last ones represent the children. *)
and operator =
  | Scan of expression
  | Select of expression * expression
  | Project of expression * expression
  | Sort of expression * expression
  | Topk of expression * expression
  | Group of expression * expression * expression
  | Join of expression * expression * expression

(* Expressions. *)
and expression =
  | FVar of string
  | Var of int
  | Lam of expression
  | App of expression * expression
  | Val of value
  | Fun of fun_builtin
  | Nil
  | Cons of expression * expression
  | TNil
  | TCons of string * expression * expression
  | Destr of expression * expression * expression
  | TDestr of expression * string
  | Exists of expression
  | Truffle
  | Dataref of string
  | Operator of operator


(** Returns the string representation of an expression *)
val string_from_expr : expression -> string
