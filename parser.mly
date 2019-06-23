%{
(* Header - OCaml declarations *)

open Lowlang

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
%token DECLARENONTERMINAL
%token DECLAREATTRIBUTE
%token DOUBLECOLON
%token ATTACHATTRIBUTE
%token ON
%token EBNF
%token DECLAREPRODUCTION
%token IMPLEMENTATTRIBUTE
%token NOT
%token EQ
%token <string> STRING
%token <int> INT
%token <string> ID

%token EOF

%type <Lowlang.lowprog> program
%type <(string * string) list> childlist

%start program

%%

/* Rules */
program:
  stmts EOF { $1 }

stmts:
  stmt stmts
    { $1 :: $2 }
| stmt
    { [$1] }

stmt:
  DECLARENONTERMINAL ID
    { NonterminalDecl($2) }
| DECLAREATTRIBUTE ID DOUBLECOLON ID
    { AttributeDecl($4, $2) }
| ATTACHATTRIBUTE ID ON ID
    { AttributeAttach($2, $4) }
| DECLAREPRODUCTION ID child EBNF childlist
    { ProductionDecl($2, $3, $5) }
| IMPLEMENTATTRIBUTE ID ON ID ASSIGN exp SEMICOLON
    { AttributeImpl($4, $2, $6) }

exp:
  IF expA THEN exp ELSE exp
    { IfThenElse ($2, $4, $6) }
| expA
    { $1 }

expA:
  expA EQ expE
    { BinOp($1, Eq, $3) }
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
  NOT expF
    { UnOp($2, Not) }
| expY
    { $1 }

expY:
  expY DOT ID
    { GetAttr($1, $3) }
| expZ
    { $1 }

expZ:
  INT
    { ConstInt $1 }
| ID
    { Name $1 }
| TRUE
    { ConstBool true }
| FALSE
    { ConstBool false }
| LPAREN expE RPAREN
    { $2 }
| ID LPAREN commalist RPAREN
    { Construct ($1, $3) }
| STRING
    { ConstStr $1 }


childlist:
  child childlist
  { $1::$2 }
|
  { [] }

commalist:
  exp COMMA commalist
  { $1::$3 }
| exp
  { [$1] }
|
  { [] }

child:
  ID DOUBLECOLON ID
    { ($1, $3) }
  
%%
(* Trailer - OCaml declarations *)


