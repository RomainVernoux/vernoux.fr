open Qir

exception Reduction_error of string

type path = int list
type redex = path

module ExprSet = Set.Make (
  struct
    type t = expression
    let compare = Pervasives.compare
  end)


(** Raises an exception *)
let fail (str: string) = raise (Reduction_error str)


(** Returns the list of redexes in an expression [expr] *)
let find_all_redexes (expr: expression) : redex list =
  let rdx = ref [] in

  let rec find_in_expr (expr: expression) (path: path) : unit =
    match expr with
    (* First the redex cases *)
    | App (Lam e1, e2) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (1::1::path);
        find_in_expr e2 (2::path)
    | Destr (Nil, e1, e2) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (2::path);
        find_in_expr e2 (3::path)
    | Destr (Cons (e1, e2), e3, e4) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (1::1::path);
        find_in_expr e2 (2::1::path);
        find_in_expr e3 (2::path);
        find_in_expr e4 (3::path)
    | TDestr (TCons (_, e1, e2), _) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (2::1::path);
        find_in_expr e2 (3::1::path)
    | Fun (Add (Val (Number _), Val (Number _)))
    | Fun (Sub (Val (Number _), Val (Number _)))
    | Fun (Mul (Val (Number _), Val (Number _)))
    | Fun (Div (Val (Number _), Val (Number _)))
    | Fun (Lt (Val (Number _), Val (Number _)))
    | Fun (Lte (Val (Number _), Val (Number _))) ->
        rdx := (List.rev path) :: (!rdx)
    | Fun (And (Val (Bool _), e1)) | Fun (Or (Val (Bool _), e1)) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (2::1::path)
    | Fun (And (e1, Val (Bool _))) | Fun (Or (e1, Val (Bool _))) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (1::1::path)
    | Fun (Eq (Val (Number _), Val (Number _)))
    | Fun (Eq (Val (String _), Val (String _)))
    | Fun (Eq (Val (Bool _), Val (Bool _))) ->
        rdx := (List.rev path) :: (!rdx)
    | Fun (Ite (Val (Bool _), e1, e2)) ->
        rdx := (List.rev path) :: (!rdx);
        find_in_expr e1 (2::1::path);
        find_in_expr e2 (3::1::path)
    (* Then the non-redex cases *)
    | Lam e1 | TDestr (e1, _) | Exists e1 ->
        find_in_expr e1 (1::path)
    | App (e1, e2) | Cons (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | TCons (_, e1, e2) ->
        find_in_expr e1 (2::path);
        find_in_expr e2 (3::path)
    | Destr (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)
    | Operator operator ->
        find_in_op operator (1::path)
    | Fun f ->
        find_in_builtin f (1::path)
    | Var _ | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
        ()

  and find_in_op (operator: operator) (path: path) : unit =
    match operator with
    | Scan e1 ->
        find_in_expr e1 (1::path)
    | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | Group (e1, e2, e3) | Join (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)

  and find_in_builtin (f: fun_builtin) (path: path) : unit =
    match f with
    | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
    | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | Ite (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)
    | Avg e1 | Sum e1 ->
        find_in_expr e1 (1::path)
  in

  find_in_expr expr [];
  List.rev !rdx


(* Walks down the given path [path] in [expr], apply the given function [f] to
   the expression [e] at the end of [path] and return a copy of [expr] where
   [e] has been replaced by [f e]. *)
let apply_path (expr: expression) (path: path)
    (f: expression -> expression) : expression =

  let fail () = fail "invalid path" in

  let rec step_in_expr (expr: expression) (path: path) : expression =
    match path with [] -> f expr | n::p -> begin
      match expr with
      | Var _ | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
          fail ()
      | Lam e ->
          if n = 1 then Lam (step_in_expr e p)
          else fail ()
      | App (e1, e2) ->
          if n = 1 then App (step_in_expr e1 p, e2)
          else if n = 2 then App (e1, step_in_expr e2 p)
          else fail ()
      | Cons (e1, e2) ->
          if n = 1 then Cons (step_in_expr e1 p, e2)
          else if n = 2 then Cons (e1, step_in_expr e2 p)
          else fail ()
      | TCons (str, e1, e2) ->
          if n = 2 then TCons (str, step_in_expr e1 p, e2)
          else if n = 3 then TCons (str, e1, step_in_expr e2 p)
          else fail ()
      | Destr (e1, e2, e3) ->
          if n = 1 then Destr (step_in_expr e1 p, e2, e3)
          else if n = 2 then Destr (e1, step_in_expr e2 p, e3)
          else if n = 3 then Destr (e1, e2, step_in_expr e3 p)
          else fail ()
      | TDestr (e1, str) ->
          if n = 1 then TDestr (step_in_expr e1 p, str)
          else fail ()
      | Exists e1 ->
          if n = 1 then Exists (step_in_expr e1 p)
          else fail ()
      | Operator op1 ->
          if n = 1 then Operator (step_in_op op1 p)
          else fail ()
      | Fun f ->
          if n = 1 then Fun (step_in_builtin f p)
          else fail ()
    end

  and step_in_op (operator: operator) (path: path) : operator =
    match path with [] -> fail () | n::p -> begin
      match operator with
      | Scan e1 ->
          if n = 1 then Scan (step_in_expr e1 p)
          else fail ()
      | Select (e1, e2) ->
          if n = 1 then Select (step_in_expr e1 p, e2)
          else if n = 2 then Select (e1, step_in_expr e2 p)
          else fail ()
      | Topk (e1, e2) ->
          if n = 1 then Topk (step_in_expr e1 p, e2)
          else if n = 2 then Topk (e1, step_in_expr e2 p)
          else fail ()
      | Project (e1, e2) ->
          if n = 1 then Project (step_in_expr e1 p, e2)
          else if n = 2 then Project (e1, step_in_expr e2 p)
          else fail ()
      | Sort (e1, e2) ->
          if n = 1 then Sort (step_in_expr e1 p, e2)
          else if n = 2 then Sort (e1, step_in_expr e2 p)
          else fail ()
      | Group (e1, e2, e3) ->
          if n = 1 then Group (step_in_expr e1 p, e2, e3)
          else if n = 2 then Group (e1, step_in_expr e2 p, e3)
          else if n = 3 then Group (e1, e2, step_in_expr e3 p)
          else fail ()
      | Join (e1, e2, e3) ->
          if n = 1 then Join (step_in_expr e1 p, e2, e3)
          else if n = 2 then Join (e1, step_in_expr e2 p, e3)
          else if n = 3 then Join (e1, e2, step_in_expr e3 p)
          else fail ()
    end

  and step_in_builtin (f: fun_builtin) (path: path) : fun_builtin =
    match path with [] -> fail () | n::p -> begin
      match f with
      | Add (e1, e2) ->
          if n = 1 then Add (step_in_expr e1 p, e2)
          else if n = 2 then Add (e1, step_in_expr e2 p)
          else fail ()
      | Sub (e1, e2) ->
          if n = 1 then Sub (step_in_expr e1 p, e2)
          else if n = 2 then Sub (e1, step_in_expr e2 p)
          else fail ()
      | Mul (e1, e2) ->
          if n = 1 then Mul (step_in_expr e1 p, e2)
          else if n = 2 then Mul (e1, step_in_expr e2 p)
          else fail ()
      | Div (e1, e2) ->
          if n = 1 then Div (step_in_expr e1 p, e2)
          else if n = 2 then Div (e1, step_in_expr e2 p)
          else fail ()
      | Lt (e1, e2) ->
          if n = 1 then Lt (step_in_expr e1 p, e2)
          else if n = 2 then Lt (e1, step_in_expr e2 p)
          else fail ()
      | Lte (e1, e2) ->
          if n = 1 then Lte (step_in_expr e1 p, e2)
          else if n = 2 then Lte (e1, step_in_expr e2 p)
          else fail ()
      | And (e1, e2) ->
          if n = 1 then And (step_in_expr e1 p, e2)
          else if n = 2 then And (e1, step_in_expr e2 p)
          else fail ()
      | Or (e1, e2) ->
          if n = 1 then Or (step_in_expr e1 p, e2)
          else if n = 2 then Or (e1, step_in_expr e2 p)
          else fail ()
       | Eq (e1, e2) ->
          if n = 1 then Eq (step_in_expr e1 p, e2)
          else if n = 2 then Eq (e1, step_in_expr e2 p)
          else fail ()
      | Ite (e1, e2, e3) ->
          if n = 1 then Ite (step_in_expr e1 p, e2, e3)
          else if n = 2 then Ite (e1, step_in_expr e2 p, e3)
          else if n = 3 then Ite (e1, e2, step_in_expr e3 p)
          else fail ()
      | Avg e1 ->
          if n = 1 then Avg (step_in_expr e1 p)
          else fail ()
      | Sum e1 ->
          if n = 1 then Sum (step_in_expr e1 p)
          else fail ()
    end
  in

  step_in_expr expr path


(* Walks down the given path [path] in [expr], and compute the given function
   [f] to the expression located at the end of [path] *)
let compute_path (expr: expression) (path: path)
    (f: expression -> 'a) : 'a =

  let fail () = fail "invalid path" in

  let rec step_in_expr (expr: expression) (path: path) : 'a =
    match path with [] -> f expr | n::p -> begin
      match expr with
      | Var _ | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
          fail ()
      | Lam e1 | TDestr (e1, _) | Exists e1 ->
          if n = 1 then step_in_expr e1 p
          else fail ()
      | App (e1, e2) | Cons (e1, e2) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else fail ()
      | TCons (str, e1, e2) ->
          if n = 2 then step_in_expr e1 p
          else if n = 3 then step_in_expr e2 p
          else fail ()
      | Destr (e1, e2, e3) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else if n = 3 then step_in_expr e3 p
          else fail ()
      | Operator op1 ->
          if n = 1 then step_in_op op1 p
          else fail ()
      | Fun f ->
          if n = 1 then step_in_builtin f p
          else fail ()
    end

  and step_in_op (operator: operator) (path: path) : 'a =
    match path with [] -> fail () | n::p -> begin
      match operator with
      | Scan e1 ->
          if n = 1 then step_in_expr e1 p
          else fail ()
      | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else fail ()
      | Group (e1, e2, e3) | Join (e1, e2, e3) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else if n = 3 then step_in_expr e3 p
          else fail ()
    end

  and step_in_builtin (f: fun_builtin) (path: path) : 'a =
    match path with [] -> fail () | n::p -> begin
      match f with
      | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
      | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else fail ()
      | Ite (e1, e2, e3) ->
          if n = 1 then step_in_expr e1 p
          else if n = 2 then step_in_expr e2 p
          else if n = 3 then step_in_expr e3 p
          else fail ()
      | Avg e1 | Sum e1 ->
          if n = 1 then step_in_expr e1 p
          else fail ()
    end
  in

  step_in_expr expr path


(* Performs one step of reduction in [expr] at the given redex [rdx] *)
let one_step_reduction (expr: expression) (rdx: redex) : expression =

  let fail () = fail "invalid redex" in

  let rec shift_in_expr (e: expression) (i: int) : expression =
    match e with
    | Val _ | FVar _ | Nil | TNil | Truffle | Dataref _ ->
        e
    | Var j ->
        if j >= i then Var (j+1) else e
    | Lam e1 ->
        Lam (shift_in_expr e1 (i+1))
    | App (e1, e2) ->
        App (shift_in_expr e1 i, shift_in_expr e2 i)
    | Cons (e1, e2) ->
        Cons (shift_in_expr e1 i, shift_in_expr e2 i)
    | TCons (str, e1, e2) ->
        TCons (str, shift_in_expr e1 i, shift_in_expr e2 i)
    | Destr (e1, e2, e3) ->
        Destr (shift_in_expr e1 i, shift_in_expr e2 i, shift_in_expr e3 i)
    | TDestr (e1, str) ->
        TDestr (shift_in_expr e1 i, str)
    | Exists e1 ->
        Exists (shift_in_expr e1 i)
    | Operator op1 ->
        Operator (shift_in_op op1 i)
    | Fun f ->
        Fun (shift_in_builtin f i)

  and shift_in_op (op: operator) (i: int) : operator =
    match op with
    | Scan e1 ->
        Scan (shift_in_expr e1 i)
    | Select (e1, e2) ->
        Select (shift_in_expr e1 i, shift_in_expr e2 i)
    | Topk (e1, e2) ->
        Topk (shift_in_expr e1 i, shift_in_expr e2 i)
    | Project (e1, e2) ->
        Project (shift_in_expr e1 i, shift_in_expr e2 i)
    | Sort (e1, e2) ->
        Sort (shift_in_expr e1 i, shift_in_expr e2 i)
    | Group (e1, e2, e3) ->
        Group (shift_in_expr e1 i, shift_in_expr e2 i, shift_in_expr e3 i)
    | Join (e1, e2, e3) ->
        Join (shift_in_expr e1 i, shift_in_expr e2 i, shift_in_expr e3 i)

  and shift_in_builtin (f: fun_builtin) (i: int) : fun_builtin =
    match f with
    | Add (e1, e2) ->
        Add (shift_in_expr e1 i, shift_in_expr e2 i)
    | Sub (e1, e2) ->
        Sub (shift_in_expr e1 i, shift_in_expr e2 i)
    | Mul (e1, e2) ->
        Mul (shift_in_expr e1 i, shift_in_expr e2 i)
    | Div (e1, e2) ->
        Div (shift_in_expr e1 i, shift_in_expr e2 i)
    | Lt (e1, e2) ->
        Lt (shift_in_expr e1 i, shift_in_expr e2 i)
    | Lte (e1, e2) ->
        Lte (shift_in_expr e1 i, shift_in_expr e2 i)
    | And (e1, e2) ->
        And (shift_in_expr e1 i, shift_in_expr e2 i)
    | Or (e1, e2) ->
        Or (shift_in_expr e1 i, shift_in_expr e2 i)
    | Eq (e1, e2) ->
        Eq (shift_in_expr e1 i, shift_in_expr e2 i)
    | Ite (e1, e2, e3) ->
        Ite (shift_in_expr e1 i, shift_in_expr e2 i, shift_in_expr e3 i)
    | Avg e1 ->
        Avg (shift_in_expr e1 i)
    | Sum e1 ->
        Sum (shift_in_expr e1 i)
  in

  let shift (e : expression) : expression =
    shift_in_expr e 0
  in


  let rec subst_in_expr (e: expression) (e': expression)
      (i: int) : expression =
    match e with
    | Val _ | FVar _ | Nil | TNil | Truffle | Dataref _ ->
        e
    | Var j ->
        if i = j then e' else if i < j then Var (j-1) else e
    | Lam e1 ->
        Lam (subst_in_expr e1 (shift e') (i+1))
    | App (e1, e2) ->
        App (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Cons (e1, e2) ->
        Cons (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | TCons (str, e1, e2) ->
        TCons (str, subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Destr (e1, e2, e3) ->
        Destr (subst_in_expr e1 e' i, subst_in_expr e2 e' i,
               subst_in_expr e3 e' i)
    | TDestr (e1, str) ->
        TDestr (subst_in_expr e1 e' i, str)
    | Exists e1 ->
        Exists (subst_in_expr e1 e' i)
    | Operator op1 ->
        Operator (subst_in_op op1 e' i)
    | Fun f ->
        Fun (subst_in_builtin f e' i)

  and subst_in_op (operator: operator) (e': expression) (i: int) : operator =
    match operator with
    | Scan e1 ->
        Scan (subst_in_expr e1 e' i)
    | Select (e1, e2) ->
        Select (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Topk (e1, e2) ->
        Topk (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Project (e1, e2) ->
        Project (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Sort (e1, e2) ->
        Sort (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Group (e1, e2, e3) ->
        Group (subst_in_expr e1 e' i, subst_in_expr e2 e' i,
               subst_in_expr e3 e' i)
    | Join (e1, e2, e3) ->
        Join (subst_in_expr e1 e' i, subst_in_expr e2 e' i,
               subst_in_expr e3 e' i)

  and subst_in_builtin (f: fun_builtin) (e': expression)
      (i: int) : fun_builtin =
    match f with
    | Add (e1, e2) ->
        Add (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Sub (e1, e2) ->
        Sub (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Mul (e1, e2) ->
        Mul (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Div (e1, e2) ->
        Div (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Lt (e1, e2) ->
        Lt (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Lte (e1, e2) ->
        Lte (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | And (e1, e2) ->
        And (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Or (e1, e2) ->
        Or (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Eq (e1, e2) ->
        Eq (subst_in_expr e1 e' i, subst_in_expr e2 e' i)
    | Ite (e1, e2, e3) ->
        Ite (subst_in_expr e1 e' i, subst_in_expr e2 e' i,
             subst_in_expr e3 e' i)
    | Avg e1 ->
        Avg (subst_in_expr e1 e' i)
    | Sum e1 ->
        Sum (subst_in_expr e1 e' i)
  in

  let reduce (expr: expression) : expression =
    match expr with
    | App (Lam e1, e2) ->
        subst_in_expr e1 e2 0
    | Destr (Nil, e1, e2) ->
        e1
    | Destr (Cons (e1, e2), e3, e4) ->
        App (App (e4, e1), e2)
    | TDestr (TCons (attr1, e1, e2), attr2) ->
        if attr1 = attr2 then e1 else TDestr (e2, attr2)
    | Fun (Add (Val (Number n1), Val (Number n2))) ->
        Val (Number (n1 + n2))
    | Fun (Sub (Val (Number n1), Val (Number n2))) ->
        Val (Number (n1 - n2))
    | Fun (Mul (Val (Number n1), Val (Number n2))) ->
        Val (Number (n1 * n2))
    | Fun (Div (Val (Number n1), Val (Number n2))) ->
        Val (Number (n1 / n2))
    | Fun (Lt (Val (Number n1), Val (Number n2))) ->
        Val (Bool (n1 < n2))
    | Fun (Lte (Val (Number n1), Val (Number n2))) ->
        Val (Bool (n1 <= n2))
    | Fun (And (Val (Bool b), e1)) | Fun (And (e1, Val (Bool b))) ->
        if b then e1 else Val (Bool false)
    | Fun (Or (Val (Bool b), e1)) | Fun (Or (e1, Val (Bool b))) ->
        if b then Val (Bool true) else e1
    | Fun (Eq (Val (Number n1), Val (Number n2))) ->
        Val (Bool (n1 = n2))
    | Fun (Eq (Val (String n1), Val (String n2))) ->
        Val (Bool (n1 = n2))
    | Fun (Eq (Val (Bool n1), Val (Bool n2))) ->
        Val (Bool (n1 = n2))
    | Fun (Ite (Val (Bool b), e1, e2)) ->
        if b then e1 else e2
    | _ ->
        fail ()
  in

  apply_path expr rdx reduce



(*****************************************************************************
 *                         Greedy reduction                                  *
 *****************************************************************************)

(** Reduces a term greedily (lists all redexes and contracts the first one
    until no redex remains). This method might not terminate for non strongly-
    normalizing terms *)
let rec greedy_reduce (expr: expression) : expression =
  match find_all_redexes expr with
  | [] ->
      expr
  | rdx::tl ->
      let new_expr = one_step_reduction expr rdx in
      greedy_reduce new_expr



(*****************************************************************************
 *                       Exhaustive reduction                                *
 *****************************************************************************)

let count_comp_operators (expr: expression) : int * int =

  let rec count_in_expr expr =
    match expr with
    | Val _ | FVar _ | Nil | TNil | Truffle | Dataref _ | Var _ ->
        (0, 0)
    | Lam e1 | TDestr (e1, _) | Exists e1 ->
        count_in_expr e1
    | App (e1, e2) | Cons (e1, e2) | TCons (_, e1, e2) ->
        Utils.add_pair (count_in_expr e1) (count_in_expr e2)
    | Destr (e1, e2, e3) ->
        Utils.add_pair (count_in_expr e1) (Utils.add_pair
          (count_in_expr e2) (count_in_expr e3))
    | Operator op1 ->
        let is_compatible = Compat_sql.compatible_operator op1 in
        Utils.add_pair (count_in_op op1) (1, if is_compatible then 1 else 0)
    | Fun f ->
        count_in_builtin f

  and count_in_op operator =
    match operator with
    | Scan e1 ->
        count_in_expr e1
    | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
        Utils.add_pair (count_in_expr e1) (count_in_expr e2)
    | Group (e1, e2, e3) | Join (e1, e2, e3) ->
        Utils.add_pair (count_in_expr e1) (Utils.add_pair
          (count_in_expr e2) (count_in_expr e3))

  and count_in_builtin f =
    match f with
    | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
    | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
        Utils.add_pair (count_in_expr e1) (count_in_expr e2)
    | Ite (e1, e2, e3) ->
        Utils.add_pair (count_in_expr e1) (Utils.add_pair
          (count_in_expr e2) (count_in_expr e3))
    | Avg e1 | Sum e1 ->
        count_in_expr e1
  in

  count_in_expr expr


let count_fragments (expr: expression) : int =

  let rec count_in_expr expr inside_fragment =
    match expr with
    | Val _ | FVar _ | Nil | TNil | Truffle | Dataref _ | Var _ ->
        0
    | Lam e1 | TDestr (e1, _) | Exists e1 ->
        count_in_expr e1 false
    | App (e1, e2) | Cons (e1, e2) | TCons (_, e1, e2) ->
        (count_in_expr e1 false) + (count_in_expr e2 false)
    | Destr (e1, e2, e3) ->
        (count_in_expr e1 false) + (count_in_expr e2 false)
        + (count_in_expr e3 false)
    | Operator op1 ->
        let is_compatible = Compat_sql.compatible_operator op1 in
        let cnt = if (inside_fragment || (not is_compatible)) then 0 else 1 in
        count_in_op op1 is_compatible + cnt
    | Fun f ->
        count_in_builtin f

  and count_in_op operator is_compatible =
    match operator with
    | Scan e1 ->
        count_in_expr e1 false
    | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
        (count_in_expr e1 false) + (count_in_expr e2 is_compatible)
    | Group (e1, e2, e3) ->
        (count_in_expr e1 false) + (count_in_expr e2 false)
        + (count_in_expr e3 is_compatible)
    | Join (e1, e2, e3) ->
        (count_in_expr e1 false) + (count_in_expr e2 true)
        + (count_in_expr e3 is_compatible)

  and count_in_builtin f =
    match f with
    | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
    | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
        (count_in_expr e1 false) + (count_in_expr e2 false)
    | Ite (e1, e2, e3) ->
        (count_in_expr e1 false) + (count_in_expr e2 false)
        + (count_in_expr e3 false)
    | Avg e1 | Sum e1 ->
        (count_in_expr e1 false)
  in

  count_in_expr expr false


(** Computes the measure for an expression (cf. specification) *)
let measure (expr: expression) : int * int * int =
  let (ops, comp) = count_comp_operators expr in
  let frags = count_fragments expr in
  (ops, comp, frags)


(** Considers all the ways to reduce a term and keeps one that has minimal
    measure (cf. specification) *)
let exhaustive_reduce (expr: expression) : expression =
  let ops, comp, frags = measure expr in
  Printf.printf "#Operators: %d, #Compatible: %d, #Fragments: %d\n"
    ops comp frags;
  flush stdout;

  let rec iter candidates pending =
    let current = ExprSet.choose pending in
    let pending = ExprSet.remove current pending in
    let candidates = ExprSet.add current candidates in
    let rdx = find_all_redexes current in
    let reduced = List.map (one_step_reduction current) rdx in
    let pending = List.fold_left (fun pending e -> ExprSet.add e pending)
      pending reduced
    in
    if ExprSet.is_empty pending then candidates else iter candidates pending
  in

  let candidates = iter ExprSet.empty (ExprSet.add expr (ExprSet.empty)) in
  let candidate_list = ExprSet.elements candidates in

  let m expr =
    let ops, comp, frags = measure expr in
    (ops - comp, frags)
  in

  let argmin candidates =
    let rec argmin_aux candidates min_m min_exprs =
      match candidates with
      | [] ->
          min_exprs
      | hd::tl ->
          let m_hd = m hd in
          if m_hd < min_m then argmin_aux tl m_hd [hd]
          else if m_hd = min_m then argmin_aux tl min_m (hd::min_exprs)
          else argmin_aux tl min_m min_exprs
    in
    argmin_aux candidates (max_int, max_int) []
  in

  let min_exprs = argmin candidate_list in

  if List.length min_exprs = 1 then begin
    Printf.printf "Found 1 reduced form with minimal measure\n"
  end else begin
    Printf.printf "Found %d reduced forms with minimal measure, here is one\n"
    (List.length min_exprs)
  end;
  flush stdout;

  let result = List.hd min_exprs in
  let ops, comp, frags = measure result in
  Printf.printf "#Operators: %d, #Compatible: %d, #Fragments: %d\n"
    ops comp frags;
  flush stdout;

  result


(*****************************************************************************
 *                        Heuristic reduction                                *
 *****************************************************************************)

exception Heuristic_exn

(** Returns the list of operators in an expression [expr] *)
let find_all_ops (expr: expression) : path list =
  let rdx = ref [] in

  let rec find_in_expr (expr: expression) (path: path) : unit =
    match expr with
    | Lam e1 | TDestr (e1, _) | Exists e1 ->
        find_in_expr e1 (1::path)
    | App (e1, e2) | Cons (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | TCons (_, e1, e2) ->
        find_in_expr e1 (2::path);
        find_in_expr e2 (3::path)
    | Destr (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)
    | Operator operator ->
        rdx := (List.rev path) :: (!rdx);
        find_in_op operator (1::path)
    | Fun f ->
        find_in_builtin f (1::path)
    | Var _ | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
        ()

  and find_in_op (operator: operator) (path: path) : unit =
    match operator with
    | Scan e1 ->
        find_in_expr e1 (1::path)
    | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | Group (e1, e2, e3) | Join (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)

  and find_in_builtin (f: fun_builtin) (path: path) : unit =
    match f with
    | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
    | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path)
    | Ite (e1, e2, e3) ->
        find_in_expr e1 (1::path);
        find_in_expr e2 (2::path);
        find_in_expr e3 (3::path)
    | Avg e1 | Sum e1 ->
        find_in_expr e1 (1::path)
  in

  find_in_expr expr [];
  !rdx

(** Returns the next redex to contract in [e] in order to inline a variable
    located at [path] in [e]. See specification for an explanation of this
    algorithm *)
let rec redex_to_inline_var (e: expression) (path: path) : redex =

  let fail () = fail "invalid path" in

  let rec inline_var (expr: expression) (path_below: path)
      (path_above: path) : (path option * int * bool) =
    match path_below with
    | [] ->
        begin
          match expr with Var i -> (None, i, false) | _ -> fail ()
        end
    | path_step::path_tail ->
        step_in_expr expr path_step path_tail path_above

  and step_in_expr (expr: expression) (n: int) (path_down: path)
      (path_up: path) : (path option * int * bool) =
    match expr with
    | Var _ | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
        fail ()
    | Lam e ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (None, 0, next_red)
          else if dist_to_var = 0 then
            (None, 0, true)
          else
            (None, dist_to_var - 1, false)
        end else fail ()
    | App (e1, e2) ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else if n = 2 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e2 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else fail ()
    | Cons (e1, e2) ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (None, 0, true)
          else
            (None, dist_to_var, false)
        end else if n = 2 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e2 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (None, 0, true)
          else
            (None, dist_to_var, false)
        end else fail ()
    | TCons (str, e1, e2) ->
        if n = 2 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (None, 0, true)
          else
            (None, dist_to_var, false)
        end else if n = 3 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e2 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (None, 0, true)
          else
            (None, dist_to_var, false)
        end else fail ()
    | Destr (e1, e2, e3) ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else if n = 2 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e2 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else if n = 3 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e3 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else fail ()
    | TDestr (e1, str) ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else fail ()
    | Exists e1 ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            inline_var e1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            raise Heuristic_exn
          else
            (None, dist_to_var, false)
        end else fail ()
    | Operator op1 ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            step_in_op op1 path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            raise Heuristic_exn
          else
            (None, dist_to_var, false)
        end else fail ()
    | Fun f ->
        if n = 1 then begin
          let (rdx, dist_to_var, next_red) =
            step_in_builtin f path_down (n::path_up)
          in
          if rdx <> None then
            (rdx, 0, false)
          else if next_red then
            (Some (make_redex e (List.rev path_up)), 0, false)
          else
            (None, dist_to_var, false)
        end else fail ()

  and step_in_op (operator: operator) (path_down: path)
      (path_up: path) : (path option * int * bool) =
    match path_down with [] -> raise Heuristic_exn | n::path_down_tl -> begin
      match operator with
      | Scan e1 ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else fail ()
      | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else if n = 2 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e2 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else fail ()
      | Group (e1, e2, e3) | Join (e1, e2, e3) ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else if n = 2 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e2 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else if n = 3 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e3 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else fail ()
    end

  and step_in_builtin (f: fun_builtin) (path_down: path)
      (path_up: path) : (path option * int * bool) =
    match path_down with [] -> fail () | n::path_down_tl -> begin
      match f with
      | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
      | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else if n = 2 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e2 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else fail ()
      | Ite (e1, e2, e3) ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else if n = 2 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e2 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              (None, 0, next_red)
            else
              (None, dist_to_var, false)
          end else if n = 3 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e3 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              (None, 0, next_red)
            else
              (None, dist_to_var, false)
          end else fail ()
      | Avg e1 | Sum e1 ->
          if n = 1 then begin
            let (rdx, dist_to_var, next_red) =
              inline_var e1 path_down_tl (n::path_up)
            in
            if rdx <> None then
              (rdx, 0, false)
            else if next_red then
              raise Heuristic_exn
            else
              (None, dist_to_var, false)
          end else fail ()
    end
  in

  let (rdx_opt, _, _) = inline_var e path [] in
  match rdx_opt with
  | Some rdx ->
      rdx
  | _ ->
      raise Heuristic_exn


(** Returns the redex at the given path, or the redex that needs to be reduced
    in order to have a redex at the given path. *)
and make_redex (expr: expression) (path: path) : redex =

  let rec aux path e =
    match e with
    | App (Lam _, _) | Destr (Nil, _, _) | Destr (Cons (_, _), _, _)
    | TDestr (TCons (_, _, _), _) | Fun (Ite (Val (Bool _), _, _))
    | Fun (Add (Val (Number _), Val (Number _)))
    | Fun (Sub (Val (Number _), Val (Number _)))
    | Fun (Mul (Val (Number _), Val (Number _)))
    | Fun (Div (Val (Number _), Val (Number _)))
    | Fun (Lt (Val (Number _), Val (Number _)))
    | Fun (Lte (Val (Number _), Val (Number _)))
    | Fun (And (Val (Bool _), _)) | Fun (Or (Val (Bool _), _))
    | Fun (And (_, Val (Bool _))) | Fun (Or (_, Val (Bool _)))
    | Fun (Eq (Val (Number _), Val (Number _)))
    | Fun (Eq (Val (String _), Val (String _)))
    | Fun (Eq (Val (Bool _), Val (Bool _))) ->
        path
    | App (x, _) ->
        aux (path @ [1]) x
    | Destr (x, _, _) ->
        aux (path @ [1]) x
    | TDestr (x, _) ->
        aux (path @ [1]) x
    | Fun (Ite (x, _, _)) | Fun (And (x, _)) | Fun (Or (x, _))
    | Fun (Add (x, Val (Number _))) | Fun (Sub (x, Val (Number _)))
    | Fun (Mul (x, Val (Number _))) | Fun (Div (x, Val (Number _)))
    | Fun (Lt (x, Val (Number _))) | Fun (Lte (x, Val (Number _)))
    | Fun (Eq (x, Val (Number _))) | Fun (Eq (x, Val (String _)))
    | Fun (Eq (x, Val (Bool _))) ->
        aux (path @ [1;1]) x
    | Fun (Add (Val (Number _), x)) | Fun (Sub (Val (Number _), x))
    | Fun (Mul (Val (Number _), x)) | Fun (Div (Val (Number _), x))
    | Fun (Lt (Val (Number _), x)) | Fun (Lte (Val (Number _), x))
    | Fun (Eq (Val (Number _), x)) | Fun (Eq (Val (String _), x))
    | Fun (Eq (Val (Bool _), x)) ->
        aux (path @ [1;2]) x
    | Var _ ->
        redex_to_inline_var expr path
    | _ ->
        raise Heuristic_exn
  in

  compute_path expr path (aux path)




(** Returns the paths of all unbound variables in [expr] *)
let find_free_vars (expr: expression) : path list =

  let rdx = ref [] in

  let rec find_in_expr (expr: expression) (var_ind: int) (path: path) : unit =
    match expr with
    | Var i ->
        if i >= var_ind then rdx := (List.rev path) :: (!rdx)
    | Lam e1 ->
        find_in_expr e1 (var_ind + 1) (1::path)
    | App (e1, e2) | Cons (e1, e2) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path)
    | TCons (_, e1, e2) ->
        find_in_expr e1 var_ind (2::path);
        find_in_expr e2 var_ind (3::path)
    | Destr (e1, e2, e3) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path);
        find_in_expr e3 var_ind (3::path)
    | TDestr (e1, _) | Exists e1 ->
        find_in_expr e1 var_ind (1::path)
    | Operator operator ->
        find_in_op operator var_ind (1::path)
    | Fun f ->
        find_in_builtin f var_ind (1::path)
    | FVar _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
        ()

  and find_in_op (operator: operator) (var_ind: int) (path: path) : unit =
    match operator with
    | Scan e1 ->
        find_in_expr e1 var_ind (1::path)
    | Select (e1, e2) | Project (e1, e2) | Sort (e1, e2) | Topk (e1, e2) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path)
    | Group (e1, e2, e3) | Join (e1, e2, e3) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path);
        find_in_expr e3 var_ind (3::path)

  and find_in_builtin (f: fun_builtin) (var_ind: int) (path: path) : unit =
    match f with
    | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) | Lt (e1, e2)
    | Lte (e1, e2) | And (e1, e2) | Or (e1, e2) | Eq (e1, e2) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path)
    | Ite (e1, e2, e3) ->
        find_in_expr e1 var_ind (1::path);
        find_in_expr e2 var_ind (2::path);
        find_in_expr e3 var_ind (3::path)
    | Avg e1 | Sum e1 ->
        find_in_expr e1 var_ind (1::path)
  in

  find_in_expr expr 0 [];
  !rdx



(** Uses an heuristic to find a reduced form of the input expression that has
    a small measure. The number of reduction steps is bounded by an integer
    constant (cf. specification) *)
let heuristic_reduce (expr: expression) (fuel_max: int) : expression =

  let fail () = fail "invalid redex" in

  let inline_one_var_in_op_config (expr: expression)
      (op_path: path) : redex option =

    let aux (e: expression) : redex option =
      let rec inline_free_vars expr free_vars_paths =
        match free_vars_paths with
        | path::tl ->
            begin
              try (
                Some (redex_to_inline_var expr path)
              ) with Heuristic_exn ->
                inline_free_vars expr tl
            end
        | [] -> None
      in
      match e with
      | Operator (Scan e1) | Operator (Select (e1, _))
      | Operator (Project (e1, _)) | Operator (Sort (e1, _))
      | Operator (Topk (e1, _)) | Operator (Join (e1, _, _))->
          let expr_path = op_path @ [1;1] in
          let free_vars = find_free_vars e1 in
          let free_vars_paths = List.map (fun p -> expr_path @ p) free_vars in

          inline_free_vars expr free_vars_paths
      | Operator (Group (e1, e2, _)) ->
          let expr_path_1 = op_path @ [1;1] in
          let expr_path_2 = op_path @ [1;2] in
          let free_vars_1 = find_free_vars e1 in
          let free_vars_2 = find_free_vars e2 in
          let free_vars_paths =
            (List.map (fun p -> expr_path_1 @ p) free_vars_1) @
            (List.map (fun p -> expr_path_2 @ p) free_vars_2)
          in

          inline_free_vars expr free_vars_paths
      | _ ->
          fail ()
    in

    compute_path expr op_path aux
  in


  let reduce_one_redex_in_op_config (expr: expression)
      (op_path: path) : redex option =

     let aux (e: expression) : redex option =
       match find_all_redexes e with
       | [] ->
           None
       | rdx::_ ->
           Some (op_path @ rdx)
     in

     compute_path expr op_path aux
  in


  let one_red_in_config (expr: expression)
      (op_path: path) : expression option =
    match inline_one_var_in_op_config expr op_path with
    | Some rdx ->
        Some (one_step_reduction expr rdx)
    | None ->
        begin
          match reduce_one_redex_in_op_config expr op_path with
          | Some rdx ->
              Some (one_step_reduction expr rdx)
          | None ->
              None
        end
  in


  let rec hred_config (original_expr: expression) (original_op_paths: path list)
      (current_expr: expression) (current_op_paths: path list)
      (fuel: int) : expression =

    if fuel = 0 then begin
      match original_op_paths with
      | [] ->
          original_expr
      | _::other_op_paths ->
          hred_config original_expr other_op_paths original_expr other_op_paths
            fuel_max
    end else begin
      match current_op_paths with
      | [] ->
          original_expr
      | next_op_path::other_op_paths ->
          begin
            match (one_red_in_config current_expr next_op_path) with
            | Some candidate_expr ->
                let (ops, comp, frags) = measure original_expr in
                let (ops', comp', frags') = measure candidate_expr in
                if (ops' - comp', frags') < (ops - comp, frags) then begin
                  let candidate_op_paths = find_all_ops candidate_expr in
                  hred_config candidate_expr candidate_op_paths candidate_expr
                    candidate_op_paths fuel_max
                end else begin
                  let candidate_op_paths = find_all_ops candidate_expr in
                  hred_config original_expr original_op_paths candidate_expr
                    candidate_op_paths (fuel - 1)
                end
            | None ->
                hred_config original_expr original_op_paths current_expr
                  other_op_paths fuel
          end
    end
  in


  let get_redex_in_child (expr: expression)
      (op_path: path) : redex option =

    let aux (e: expression) : redex option =
      match e with
      | Operator (Scan _) ->
          None
      | Operator (Select (_, _)) | Operator (Project (_, _))
      | Operator (Sort (_, _)) | Operator (Topk (_, _)) ->
          begin
            let expr_path = op_path @ [1;2] in
            try (Some (make_redex expr expr_path)) with _ -> None
          end
      | Operator (Join (_, _, _)) ->
          begin
            let expr_path = op_path @ [1;2] in
            try (Some (make_redex expr expr_path)) with _ ->
              begin
                let expr_path = op_path @ [1;3] in
                try (Some (make_redex expr expr_path)) with _ -> None
              end
          end
      | Operator (Group (_ ,_ , e1)) ->
          begin
            let expr_path = op_path @ [1;3] in
            try (Some (make_redex expr expr_path)) with _ -> None
          end
      | _ ->
          fail ()
    in

    compute_path expr op_path aux
  in

  let one_red_in_child (expr: expression)
      (op_path: path) : expression option =
    match get_redex_in_child expr op_path with
    | Some rdx ->
        Some (one_step_reduction expr rdx)
    | None ->
        None
  in


  let rec hred_child (original_expr: expression) (original_op_paths: path list)
      (current_expr: expression) (current_op_paths: path list)
      (fuel: int) : expression =

    if fuel = 0 then begin
      match original_op_paths with
      | [] ->
          original_expr
      | _::other_op_paths ->
          hred_child original_expr other_op_paths original_expr other_op_paths
            fuel_max
    end else begin
      match current_op_paths with
      | [] ->
          original_expr
      | next_op_path::other_op_paths ->
          begin
            match (one_red_in_child current_expr next_op_path) with
            | Some candidate_expr ->
                let (ops, comp, frags) = measure original_expr in
                let (ops', comp', frags') = measure candidate_expr in
                if (ops' - comp', frags') < (ops - comp, frags) then begin
                  let candidate_op_paths = find_all_ops candidate_expr in
                  hred_child candidate_expr candidate_op_paths candidate_expr
                    candidate_op_paths fuel_max
                end else begin
                  let candidate_op_paths = find_all_ops candidate_expr in
                  hred_child original_expr original_op_paths candidate_expr
                    candidate_op_paths (fuel - 1)
                end
            | None ->
                hred_child original_expr original_op_paths current_expr
                  other_op_paths fuel
          end
    end
  in


  let ops, comp, frags = measure expr in
  Printf.printf "#Operators: %d, #Compatible: %d, #Fragments: %d\n"
    ops comp frags;
  flush stdout;

  print_string (string_from_expr expr); print_newline ();

  let ops_path = find_all_ops expr in
  let result = hred_config expr ops_path expr ops_path fuel_max in

  let ops_path = find_all_ops result in
  let result = hred_child result ops_path result ops_path fuel_max in

  let ops, comp, frags = measure result in
  Printf.printf "#Operators: %d, #Compatible: %d, #Fragments: %d\n"
    ops comp frags;
  flush stdout;

  result
