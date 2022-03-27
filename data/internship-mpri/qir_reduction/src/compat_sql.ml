open Qir

let one_var = [0]

let two_vars = [0;1]

let rec supported_expression (expr: expression) (vars: int list): bool =
  match expr with
  | Val _ ->
      true
  | TDestr (Var i, _) ->
      List.mem i vars
  | Fun (Add (e1, e2)) | Fun (Sub (e1, e2)) | Fun (Mul (e1, e2))
  | Fun (Div (e1, e2)) | Fun (Lt (e1, e2)) | Fun (Lte (e1, e2))
  | Fun (And (e1, e2)) | Fun (Or (e1, e2)) | Fun (Eq (e1, e2)) ->
      (supported_expression e1 vars) && (supported_expression e2 vars)
  | Fun (Ite (e1, e2, e3)) ->
      (supported_expression e1 vars) && (supported_expression e2 vars)
      && (supported_expression e3 vars)
  | Exists e1 ->
      compat_op_tree e1
  | _ ->
      false

and tuple_cons (expr: expression) : bool =
  match expr with
  | TNil ->
      true
  | TCons (str, e1, e2) ->
      (supported_expression e1 one_var) && (tuple_cons e2)
  | _ ->
      false

and list_cons (expr: expression) : bool =
  match expr with
  | Nil ->
      true
  | Cons (e1, e2) ->
      (supported_expression e1 one_var) && (list_cons e2)
  | _ ->
      false

and scan_expr (expr: expression) : bool =
  match expr with
  | Dataref _ ->
      true
  | _ ->
      false

and select_expr (expr: expression) : bool =
  match expr with
  | Lam e1 ->
      supported_expression e1 one_var
  | _ ->
      false

and project_expr (expr: expression) : bool =
  match expr with
  | Lam (Var 0) ->
      true
  | Lam e1 ->
      tuple_cons e1
  | _ ->
      false

and sort_expr (expr: expression) : bool =
  match expr with
  | Lam e1 ->
      list_cons e1
  | _ ->
      false

and topk_expr (expr: expression) : bool =
  supported_expression expr one_var

and join_expr (expr: expression) : bool =
  match expr with
  | Lam (Lam e1) ->
      supported_expression e1 two_vars
  | _ ->
      false

and group_eq_expr (expr: expression) : bool =
  match expr with
  | Lam e1 ->
      list_cons e1
  | _ ->
      false

and agg (expr: expression) : bool =
  match expr with
  | Fun (Avg e1) | Fun (Sum e1) ->
      supported_expression e1 one_var
  | _ ->
      false

and tuple_cons_agg (expr: expression) : bool =
  match expr with
  | TNil ->
      true
  | TCons(str, e1, e2) ->
      (agg e1) && (tuple_cons_agg e2)
  | _ ->
      false

and group_agg_expr (expr: expression) : bool =
  match expr with
  | Lam e1 ->
      tuple_cons_agg e1
  | _ ->
      false

and group_expr (expr1: expression) (expr2: expression) : bool =
  (group_eq_expr expr1) && (group_agg_expr expr2)

(** Tells if an operator is compatible with a SQL database. See specification
    for a formal definition *)
and compatible_operator (operator: operator) : bool =
  match operator with
  | Scan e1 ->
      scan_expr e1
  | Select (e1, e2) ->
      select_expr e1
  | Project (e1, e2) ->
      project_expr e1
  | Sort (e1, e2) ->
      sort_expr e1
  | Topk (e1, e2) ->
      topk_expr e1
  | Group (e1, e2, e3) ->
      group_expr e1 e2
  | Join (e1, e2, e3) ->
      join_expr e1

(** Tells if an expression is a tree of compatible operators *)
and compat_op_tree (expr: expression) : bool =
  match expr with
  | Operator ((Scan _) as op) ->
      compatible_operator op
  | Operator ((Select (_, e1)) as op) | Operator ((Project (_, e1)) as op)
  | Operator ((Sort (_, e1)) as op) | Operator ((Topk (_, e1)) as op)
  | Operator ((Group (_, _, e1)) as op) ->
      (compatible_operator op) && (compat_op_tree e1)
  | Operator ((Join (_, e1, e2)) as op) ->
      (compatible_operator op) && (compat_op_tree e1) && (compat_op_tree e2)
  | _ ->
      false
