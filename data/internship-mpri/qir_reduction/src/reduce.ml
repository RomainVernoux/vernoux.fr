type reduce_mode =
 | Echo              (* Prints the input as is *)
 | CallByName        (* Reduces the outer-left-most redex *)
 | Exhaustive        (* Exhaustive evaluation, cf. specification *)
 | Heuristic of int  (* Heuristic evaluation, cf. specification *)

let mode = ref Echo

(* Parsing of the command-line options *)
let spec_list = [
  ("-echo", Arg.Unit (fun () -> mode := Echo),
   " Prints the input as is");
  ("-cbn", Arg.Unit (fun () -> mode := CallByName),
   " Reduces the outer-left-most redex (call-by-name)");
  ("-exhaustive", Arg.Unit (fun () -> mode := Exhaustive),
   " Exhaustive evaluation, cf. specification");
  ("-heuristic", Arg.Int (fun n -> mode := Heuristic n),
   " Heuristic evaluation, cf. specification");
]

let usage_msg = "Usage: reduce [OPTION]. The input expression is read from stdin.\n"
  ^ "Default is 'reduce -echo'"

let _ = Arg.parse spec_list (fun _ -> ()) usage_msg

let _ =
    let lexbuf = Lexing.from_channel stdin in
    let parsed = Parser.main_expr Lexer.token lexbuf in
    let reduced =
      match !mode with
      | Echo ->
          parsed
      | CallByName ->
          Qir_reduction.greedy_reduce parsed
      | Exhaustive ->
          Qir_reduction.exhaustive_reduce parsed
      | Heuristic n ->
          Qir_reduction.heuristic_reduce parsed n
    in
    print_string (Qir.string_from_expr reduced); print_newline(); flush stdout
