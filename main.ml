open Corelang
open Lowlang
open Oi

let parse_file filename =
  let in_channel = open_in filename in
  let buffer = Lexing.from_channel in_channel in
    let lowprog = Parser.program Lex.scan buffer in
    print_endline "Successful parse\n";
    List.iter (fun x -> print_endline ([%show: lowstmt] x)) lowprog;
    let lang = raiseProg lowprog in
    print_endline ("Raised: "^([%show: language] lang));
    match lang with Language(_, _, attrs, prods, _) ->
    let mainprod = List.find (fun x -> match x with Production(n, _, _, _) -> n="Main") prods in
    let returncode = List.find (fun x -> match x with Attribute(n, _, _) -> n="exitcode") attrs in
    print_endline "Invoke...";
    let res = (getEval lang) (GetAttr (Decorate (Construct (mainprod, []), []), returncode)) in
    print_endline "\n\n";
    print_endline ([%show: value] res);
    match res with
      | BareNonterminalV(_, _, oi)
      | DecoratedNonterminalV(_, _, _, oi) ->
        print_endline "\n\nOI:";
        print_endline (string_of_oi oi)
      | _ -> ()

let () =
  if Array.length Sys.argv <> 2
  then (
    print_endline "Incorrect usage\n"
  )
  else
    parse_file Sys.argv.(1)
