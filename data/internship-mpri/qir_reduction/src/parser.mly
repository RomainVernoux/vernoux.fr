%{

open Qir

(** Substitutes a free variable with a bound variable. This parser is bottom-up
    and De Bruijn indices follow a top-down logic. This method allows to first
    parse variables as free and susbitute them with De Bruijn indices later *)
let subst_free_var (fvar: string) (expr: expression) : expression =

  let rec subst_in_expr e depth =
    match e with
    | Var _ | Val _ | Nil | TNil | Truffle | Dataref _ ->
        e
    | FVar str ->
        if str = fvar then Var depth else e
    | Lam e1 ->
        Lam (subst_in_expr e1 (depth+1))
    | App (e1, e2) ->
        App (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Cons (e1, e2) ->
        Cons (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | TCons (str, e1, e2) ->
        TCons (str, subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Destr (e1, e2, e3) ->
        Destr (subst_in_expr e1 depth, subst_in_expr e2 depth,
               subst_in_expr e3 depth)
    | TDestr (e1, str) ->
        TDestr (subst_in_expr e1 depth, str)
    | Exists e1 ->
        Exists (subst_in_expr e1 depth)
    | Operator op1 ->
        Operator (subst_in_op op1 depth)
    | Fun f ->
        Fun (subst_in_builtin f depth)

  and subst_in_op operator depth =
    match operator with
    | Scan e1 ->
        Scan (subst_in_expr e1 depth)
    | Select (e1, e2) ->
        Select (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Project (e1, e2) ->
        Project (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Sort (e1, e2) ->
        Sort (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Topk (e1, e2) ->
        Topk (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Group (e1, e2, e3) ->
        Group (subst_in_expr e1 depth, subst_in_expr e2 depth,
               subst_in_expr e3 depth)
    | Join (e1, e2, e3) ->
        Join (subst_in_expr e1 depth, subst_in_expr e2 depth,
               subst_in_expr e3 depth)

  and subst_in_builtin f depth =
    match f with
    | Add (e1, e2) ->
        Add (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Sub (e1, e2) ->
        Sub (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Mul (e1, e2) ->
        Mul (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Div (e1, e2) ->
        Div (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Lt (e1, e2) ->
        Lt (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Lte (e1, e2) ->
        Lte (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | And (e1, e2) ->
        And (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Or (e1, e2) ->
        Or (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Eq (e1, e2) ->
        Eq (subst_in_expr e1 depth, subst_in_expr e2 depth)
    | Ite (e1, e2, e3) ->
        Ite (subst_in_expr e1 depth, subst_in_expr e2 depth,
             subst_in_expr e3 depth)
    | Avg e1 ->
        Avg (subst_in_expr e1 depth)
    | Sum e1 ->
        Sum (subst_in_expr e1 depth)
  in

  subst_in_expr expr 0

(* Creates an App tree from an n-ary application *)
let make_app main_expr args =

  let first_term = App(main_expr, List.hd args) in

  let rec make subterm args =
    match args with
    | [] ->
        subterm
    | hd::tl ->
        make (App (subterm, hd)) tl
  in

  make first_term (List.tl args)

%}

%token <int> INT
%token <string> STRING
%token <string> VAR
%token <string> DATAREF
%token TRUE FALSE FUN ARROW LET IN
%token NIL TNIL CONS TCONS DESTR TDESTR EXISTS TRUFFLE
%token SCAN SELECT PROJECT SORT GROUP LIMIT JOIN
%token EQ PLUS MINUS TIMES DIV IF THEN ELSE AND OR AVG SUM LT LTE
%token LPAREN RPAREN LBRACKET RBRACKET COMMA
%token EOF

%start main_expr
%type <Qir.expression> main_expr
%%

main_expr:
    expr EOF                          { $1 }
;

expr:
  | simpl_expr                            { $1 }
  | app_expr                              { $1 }
  | lambda                                { $1 }
  | letin                                 { $1 }
;

app_expr:
    simpl_expr simpl_expr_list            { make_app $1 (List.rev $2) }
;

simpl_expr:
    LPAREN expr RPAREN                    { $2 }
  | variable                              { $1 }
  | value                                 { $1 }
  | constructor                           { $1 }
  | destructor                            { $1 }
  | exists                                { $1 }
  | operator                              { $1 }
  | builtin                               { $1 }
  | truffle                               { $1 }
  | dataref                               { $1 }
;

simpl_expr_list:
    simpl_expr                            { [$1] }
  | simpl_expr_list simpl_expr            { $2 :: $1 }
;

variable:
    VAR                                   { FVar $1 }
;

lambda:
    FUN VAR ARROW expr                    { Lam (subst_free_var $2 $4) }
;

letin:
    LET VAR EQ expr IN expr               { App (Lam (subst_free_var $2 $6), $4) }
;


value:
    INT                                   { Val (Number $1) }
  | STRING                                { Val (String $1) }
  | TRUE                                  { Val (Bool true) }
  | FALSE                                 { Val (Bool false) }
;

operator:
    SCAN LBRACKET expr RBRACKET
    LPAREN RPAREN                         { Operator (Scan $3) }
  | SELECT LBRACKET expr RBRACKET
    LPAREN expr RPAREN                    { Operator (Select ($3, $6)) }
  | LIMIT LBRACKET expr RBRACKET
    LPAREN expr RPAREN                    { Operator (Topk ($3, $6)) }
  | PROJECT LBRACKET expr RBRACKET
    LPAREN expr RPAREN                    { Operator (Project ($3, $6)) }
  | SORT LBRACKET expr RBRACKET
    LPAREN expr RPAREN                    { Operator (Sort ($3, $6)) }
  | GROUP LBRACKET expr COMMA expr
    RBRACKET LPAREN expr RPAREN           { Operator (Group ($3, $5, $8)) }
  | JOIN LBRACKET expr RBRACKET
    LPAREN expr COMMA expr RPAREN         { Operator (Join ($3, $6, $8)) }
;

builtin:
    PLUS simpl_expr simpl_expr            { Fun (Add ($2, $3)) }
  | MINUS simpl_expr simpl_expr           { Fun (Sub ($2, $3)) }
  | TIMES simpl_expr simpl_expr           { Fun (Mul ($2, $3)) }
  | DIV simpl_expr simpl_expr             { Fun (Div ($2, $3)) }
  | AND simpl_expr simpl_expr             { Fun (And ($2, $3)) }
  | LT simpl_expr simpl_expr              { Fun (Lt ($2, $3)) }
  | LTE simpl_expr simpl_expr             { Fun (Lte ($2, $3)) }
  | OR simpl_expr simpl_expr              { Fun (Or ($2, $3)) }
  | EQ simpl_expr simpl_expr              { Fun (Eq ($2, $3)) }
  | IF simpl_expr THEN simpl_expr
    ELSE simpl_expr                       { Fun (Ite ($2, $4, $6)) }
  | AVG simpl_expr                        { Fun (Avg $2) }
  | SUM simpl_expr                        { Fun (Sum $2) }
;

constructor:
    NIL                                   { Nil }
  | CONS simpl_expr simpl_expr            { Cons ($2, $3) }
  | TNIL                                  { TNil }
  | TCONS STRING simpl_expr simpl_expr    { TCons ($2, $3, $4) }
;

destructor:
    DESTR simpl_expr simpl_expr
    simpl_expr                            { Destr ($2, $3, $4) }
  | TDESTR simpl_expr STRING              { TDestr ($2, $3) }
;

exists:
    EXISTS simpl_expr                     { Exists $2 }
;

truffle:
    TRUFFLE                               { Truffle }
;

dataref:
    DATAREF                               { Dataref $1 }
;
