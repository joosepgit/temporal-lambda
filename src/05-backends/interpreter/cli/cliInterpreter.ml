include Interpreter
module PrettyPrint = Language.PrettyPrint

let view_run_state (run_state : run_state) =
  match run_state with
  | { computations = Ast.Return exp :: _; _ } ->
      Format.printf "return %t@."
        (PrettyPrint.print_expression ~max_level:0 exp)
  | _ -> ()
