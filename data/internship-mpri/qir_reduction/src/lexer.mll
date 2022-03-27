{
open Parser        (* The type token is defined in parser.mli *)
exception Eof
}
rule token = parse
    [' ' '\t' '\r' '\n']                 { token lexbuf }
  | '/' '*' [^ '*']* '*' '/'             { token lexbuf }
  | ['0'-'9']+ as lxm                    { INT(int_of_string lxm) }
  | "true"                               { TRUE }
  | "false"                              { FALSE }
  | "fun"                                { FUN }
  | "->"                                 { ARROW }
  | "let"                                { LET }
  | "in"                                 { IN }
  | "nil"                                { NIL }
  | "tnil"                               { TNIL }
  | "cons"                               { CONS }
  | "tcons"                              { TCONS }
  | "destr"                              { DESTR }
  | "tdestr"                             { TDESTR }
  | "<Truffle>"                          { TRUFFLE }
  | "db." (['a'-'z' '_']* as id)         { DATAREF(id) }
  | "Scan"                               { SCAN }
  | "Select"                             { SELECT }
  | "Project"                            { PROJECT }
  | "Sort"                               { SORT }
  | "Group"                              { GROUP }
  | "Limit"                              { LIMIT }
  | "Join"                               { JOIN }
  | "Exists"                             { EXISTS }
  | '='                                  { EQ }
  | '+'                                  { PLUS }
  | '-'                                  { MINUS }
  | '*'                                  { TIMES }
  | '/'                                  { DIV }
  | '<'                                  { LT }
  | "<="                                 { LTE }
  | "if"                                 { IF }
  | "then"                               { THEN }
  | "else"                               { ELSE }
  | "and"                                { AND }
  | "or"                                 { OR }
  | "avg"                                { AVG }
  | "sum"                                { SUM }
  | '\"'('\\'_|[^'\\''\"'])*'\"' as lxm  { STRING(lxm) }
  | ['a'-'z'] (
        ['a'-'z']
      | ['0'-'9']
      | '_'
    )* as lxm                            { VAR(lxm) }
  | '('                                  { LPAREN }
  | ')'                                  { RPAREN }
  | '['                                  { LBRACKET }
  | ']'                                  { RBRACKET }
  | ','                                  { COMMA }
  | eof                                  { EOF }
