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
%token CONCAT
%token DECLARE
%token NONTERMINAL
%token DOUBLECOLON
%token ATTRIBUTE
%token ON
%token DERIVES
%token PRODUCTION
%token ATTACH
%token SYNTHESIZED
%token INHERITED
%token NOT
%token EQ
%token DECORATE
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
  DECLARE NONTERMINAL ID
    { NonterminalDecl($3) }
| DECLARE SYNTHESIZED ATTRIBUTE ID DOUBLECOLON ID
    { AttributeDecl($6, $4, Syn) }
| DECLARE INHERITED ATTRIBUTE ID DOUBLECOLON ID
    { AttributeDecl($6, $4, Inh) }
| ATTACH ATTRIBUTE ID ON ID
    { AttributeAttach($3, $5) }
| DECLARE PRODUCTION ID child DERIVES childlist LBRACE rules RBRACE
    { ProductionDecl($3, $4, $6, $8) }

rules:
  rule rules
    { $1::$2 }
|
    { [] }

rule:
  ID DOT ID ASSIGN exp SEMICOLON
    { Rule($1, $3, $5) }

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
| expE CONCAT expT
    { BinOp ($1, Concat, $3) }
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
| DECORATE exp LBRACE decorations RBRACE
    { Decorate ($2, $4) }

decorations:
  decoration decorations
    { $1::$2 }
|
    { [] }

decoration:
  ID ASSIGN exp
    { ($1, $3) }

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


