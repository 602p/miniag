open Lang
open Print

module Driver = struct

  let parse_file filename =
    let in_channel = open_in filename in
    let buffer = Lexing.from_channel in_channel in

    try
      let result = Parser.program Scanner.scan buffer in
      print_endline "Successful parse\n";
      print_endline (reprOfValue (evalExpr [] result))
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
