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
let string_from_expr (expr: expression) : string =

  let var_count = ref 0 in

  let buf = Buffer.create 16 in

  let indent_str (indent: int) : unit =
    for i = 1 to indent do
      Buffer.add_string buf "  "
    done
  in

  let rec expr_str (expr: expression) (var_names: string list)
      (indent: int) : unit =
    match expr with
    | Var i ->
        begin
          try (
            Buffer.add_string buf (List.nth var_names i)
          ) with _ ->
            Buffer.add_string buf ("(Var " ^ (string_of_int i) ^ ")")
        end
    | FVar str ->
        Buffer.add_string buf ("FVar(" ^ str ^ ")")
    | Nil ->
        Buffer.add_string buf "nil"
    | TNil ->
        Buffer.add_string buf "tnil"
    | Truffle ->
        Buffer.add_string buf "<Truffle>"
    | Dataref str ->
        Buffer.add_string buf "db.";
        Buffer.add_string buf str
    | Lam e ->
        let var_str = "x" ^ (string_of_int !var_count) in
        incr var_count;
        let new_indent = indent + 1 in
        Buffer.add_string buf "fun ";
        Buffer.add_string buf var_str;
        Buffer.add_string buf " ->\n";
        indent_str new_indent;
        expr_str e (var_str :: var_names) new_indent;
        Buffer.add_string buf "\n";
        indent_str indent
    | App (e1, e2) ->
        Buffer.add_char buf '(';
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent;
        Buffer.add_char buf ')'
    | Cons (e1, e2) ->
        Buffer.add_string buf "(cons ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent;
        Buffer.add_char buf ')'
    | TCons (str, e1, e2) ->
        Buffer.add_string buf "(tcons ";
        Buffer.add_string buf str;
        Buffer.add_char buf ' ';
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent;
        Buffer.add_char buf ')'
    | Destr (e1, e2, e3) ->
        Buffer.add_string buf "(destr ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e3 var_names indent;
        Buffer.add_char buf ')'
    | TDestr (e1, str) ->
        Buffer.add_string buf "(tdestr ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        Buffer.add_string buf str;
        Buffer.add_char buf ')'
    | Exists e1 ->
        let new_indent = indent + 1 in
        Buffer.add_string buf "(Exists (\n";
        indent_str new_indent;
        expr_str e1 var_names new_indent;
        Buffer.add_string buf "))"
    | Val v ->
        value_str v
    | Operator op1 ->
        op_str op1 var_names indent
    | Fun f ->
        Buffer.add_char buf '(';
        builtin_str f var_names indent;
        Buffer.add_char buf ')'

  and value_str (v: value) : unit =
    match v with
    | Number n ->
        Buffer.add_string buf (string_of_int n)
    | String str ->
        Buffer.add_string buf str
    | Bool b ->
        Buffer.add_string buf (if b then "true" else "false")

  and op_str (operator: operator) (var_names: string list)
      (indent: int) : unit =
    match operator with
    | Scan e1 ->
        Buffer.add_string buf "Scan[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "]()"
    | Select (e1, e2) ->
        Buffer.add_string buf "Select[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "](";
        expr_str e2 var_names indent;
        Buffer.add_string buf ")"
    | Topk (e1, e2) ->
        Buffer.add_string buf "Limit[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "](";
        expr_str e2 var_names indent;
        Buffer.add_string buf ")"
    | Project (e1, e2) ->
        Buffer.add_string buf "Project[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "](";
        expr_str e2 var_names indent;
        Buffer.add_string buf ")"
    | Sort (e1, e2) ->
        Buffer.add_string buf "Sort[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "](";
        expr_str e2 var_names indent;
        Buffer.add_string buf ")"
    | Group (e1, e2, e3) ->
        Buffer.add_string buf "Group[";
        expr_str e1 var_names indent;
        Buffer.add_string buf ", ";
        expr_str e2 var_names indent;
        Buffer.add_string buf "](";
        expr_str e3 var_names indent;
        Buffer.add_string buf ")"
    | Join (e1, e2, e3) ->
        Buffer.add_string buf "Join[";
        expr_str e1 var_names indent;
        Buffer.add_string buf "](";
        expr_str e2 var_names indent;
        Buffer.add_string buf ", ";
        expr_str e3 var_names indent;
        Buffer.add_string buf ")"

  and builtin_str (f: fun_builtin) (var_names: string list)
      (indent: int) : unit =
    match f with
    | Add (e1, e2) ->
        Buffer.add_string buf "+ ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Sub (e1, e2) ->
        Buffer.add_string buf "- ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Mul (e1, e2) ->
        Buffer.add_string buf "* ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Div (e1, e2) ->
        Buffer.add_string buf "/ ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Lt (e1, e2) ->
        Buffer.add_string buf "< ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Lte (e1, e2) ->
        Buffer.add_string buf "<= ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | And (e1, e2) ->
        Buffer.add_string buf "and ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Or (e1, e2) ->
        Buffer.add_string buf "or ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Eq (e1, e2) ->
        Buffer.add_string buf "= ";
        expr_str e1 var_names indent;
        Buffer.add_char buf ' ';
        expr_str e2 var_names indent
    | Ite (e1, e2, e3) ->
        Buffer.add_string buf "if ";
        expr_str e1 var_names indent;
        Buffer.add_string buf " then ";
        expr_str e2 var_names indent;
        Buffer.add_string buf " else ";
        expr_str e3 var_names indent
    | Avg e1 ->
        Buffer.add_string buf "avg ";
        expr_str e1 var_names indent
    | Sum e1 ->
        Buffer.add_string buf "sum ";
        expr_str e1 var_names indent

  in expr_str expr [] 0;
  Buffer.contents buf
