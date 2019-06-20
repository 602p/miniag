{
open Parser

let lx_start = Lexing.lexeme_start
let lx_body = Lexing.lexeme

exception Lexical_error
}

rule scan = parse
  | "if"
    { IF }

  | "then"
    { THEN }

  | "else"
    { ELSE }

  | "true"
    { TRUE }

  | "false"
    { FALSE }

  | "declare nonterminal"
    { DECLARENONTERMINAL }

  | "declare attribute"
    { DECLAREATTRIBUTE }

  | "attach attribute"
    { ATTACHATTRIBUTE }

  | "declare production"
    { DECLAREPRODUCTION }

  | "implement attribute"
    { IMPLEMENTATTRIBUTE }

  | "::="
    { EBNF }

  | "on"
    { ON }

  | "::"
    { DOUBLECOLON }

  | "="
    { ASSIGN }

  | "=="
    { EQ }

  | "{"
    { LBRACE }

  | "}"
    { RBRACE }

  | "("
    { LPAREN }

  | ")"
    { RPAREN }

  | ";"
    { SEMICOLON }

  | "."
    { DOT }

  | "+"
    { PLUS }

  | "-"
    { MINUS }

  | "/"
    { DIVIDE }

  | "*"
    { TIMES }

  | ","
    { COMMA }

  | "!"
    { NOT }

  | eof 
      { EOF }

  | ['0' - '9']+
    { INT (int_of_string (lx_body lexbuf)) }

  | ['a' - 'z' 'A' - 'Z']['a' - 'z' 'A' - 'Z' '0' - '9' '_']*
    { ID (lx_body lexbuf) }

  | '\n'
    { scan lexbuf }

  | [' ' '\t' '\r'] +
    { scan lexbuf }

  | '"'
    { let str, _ = scan_string "" lexbuf in STRING (str) }

  | eof
    { EOF }

  | _ 
    { Printf.printf "illegal char"; scan lexbuf }

and scan_string sofar = parse
  | '"'
    { sofar, lexbuf }

  | "\\n"
    { scan_string (sofar ^ "\n") lexbuf }

  | "\\t"
    { scan_string (sofar ^ "\t") lexbuf }

  | "\\\""
    { scan_string (sofar ^ "\"") lexbuf }

  | "\\\\"
    { scan_string (sofar ^ "\\") lexbuf }

  | [^'\\' '"' '\n'] +
    { scan_string (sofar ^ (lx_body lexbuf)) lexbuf }

  | eof
    { print_endline
        "unterminated string";
      failwith "unterminated string (fatal)" }

  | _ 
    { print_endline
        "illegal character (string)";
      scan_string sofar lexbuf }
