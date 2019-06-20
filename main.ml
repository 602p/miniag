open Corelang
open Print
open Lowlang

module Driver = struct

  let parse_file filename =
    let in_channel = open_in filename in
    let buffer = Lexing.from_channel in_channel in

    try
      let lowprog = Parser.program Scanner.scan buffer in
      print_endline "Successful parse\n";
      List.iter (fun x -> print_endline (reprOfLowStmt x)) lowprog;
      print_endline "Raising...\n";
      let prods, attrs = raiseProg lowprog in
      let mainprod = List.assoc "Main" prods in
      let returncode = List.assoc "exitcode" attrs in
      print_endline "Invoking main...\n";
      let res = evalExpr [] (GetAttr (Construct (mainprod, []), returncode)) in
      print_endline "\n\n";
      print_endline (reprOfValue res)
    with 
    | Scanner.Lexical_error ->
       print_endline "A lexical error occurred.\n" 
    | Parsing.Parse_error ->
       print_endline "A syntax error occurred.\n" 

  let () =
    if Array.length Sys.argv <> 2
    then (
      print_endline "Incorrect usage\n"
    )
    else
      parse_file Sys.argv.(1)

end
