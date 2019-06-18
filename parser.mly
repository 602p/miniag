%{
(* Header - OCaml declarations *)

open Lang

%}

/* Declarations */

%token IF
%token THEN
%token ELSE
%token ASSIGN
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN
%token SEMICOLON
%token DOT
%token TRUE
%token FALSE
%token COMMA
%token PLUS
%token MINUS
%token DIVIDE
%token TIMES
%token <int> INT
%token <string> ID

%token EOF

%type <Lang.expr> program

%start program

%%

/* Rules */
program:
  exp EOF { $1 }

exp:
  IF exp THEN exp ELSE exp
    { IfThenElse ($2, $4, $6) }
| expE
    { $1 }

expE:
  expE PLUS expT
    { BinOp ($1, Add, $3) }
| expE MINUS expT
    { BinOp ($1, Sub, $3) }
| expT
    { $1 }

expT:
  expT TIMES expF
    { BinOp ($1, Mul, $3) }
| expT DIVIDE expF
    { BinOp ($1, Div, $3) }
| expF
    { $1 }

expF:
  INT
    { Const (IntV $1) }
| TRUE
    { Const (BoolV true) }
| FALSE
    { Const (BoolV false) }
| LPAREN expE RPAREN
    { $2 }
  
%%
(* Trailer - OCaml declarations *)


