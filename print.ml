open Corelang
open Lowlang
open Util

let reprOfBinoper = function
	| Add -> "+"
	| Sub -> "-"
	| Mul -> "*"
	| Div -> "/"
	| Concat -> "^"
	| Eq -> "=="

let reprOfUnoper = function
	| Not -> "!"
	| Neg -> "-"

let rec reprOfValue = function
	| StringV x -> "StringV(\"" ^ x ^ "\")"
	| IntV x -> "IntV(" ^ (string_of_int x) ^ ")"
	| BoolV true -> "BoolV(true)"
	| BoolV false -> "BoolV(false)"
	| UnitV -> "UnitV"
	| NonterminalV (_, _, _) -> "NonterminalV(...)"
	| TerminalV (_, _) -> "TerminalV(...)"

let rec reprOfLowExpr = function
	| ConstInt x -> "ConstInt(" ^ (string_of_int x) ^ ")"
	| ConstBool true -> "ConstBool(true)"
	| ConstBool false -> "ConstBool(false)"
	| ConstStr x -> "ConstString(\"" ^ x ^ "\")"
	| BinOp (l, op, r) -> "BinOp("^(reprOfLowExpr l)^", "^(reprOfBinoper op)^", "^(reprOfLowExpr r)^")"
	| UnOp (a, op) -> "UnOp("^(reprOfLowExpr a)^", "^(reprOfUnoper op)^")"
	| IfThenElse (c, t, f) -> "IfThenElse("^(reprOfLowExpr c)^", "^(reprOfLowExpr t)^", "^(reprOfLowExpr f)^")"
	| Construct (p, a) -> "Construct("^p^", ["^(stringJoin ", " (List.map reprOfLowExpr a))^"])"
	| GetAttr (v, a) -> "GetAttr("^(reprOfLowExpr v)^", "^a^")"
	| Name x -> "Name("^x^")"

let reprOfLowStmt = function
	| NonterminalDecl name -> "NonterminalDecl("^name^")"
	| AttributeDecl (ty, at) -> "AttributeDecl("^ty^", "^at^")"
	| AttributeAttach (at, nt) -> "AttributeAttach("^at^", "^nt^")"
	| ProductionDecl (prname, nt, children) -> "ProductionDecl("^prname^", "^nt^", ["^(stringJoin ", " (List.map (fun (x, y) -> "("^x^", "^y^")") children))^"])"
	| AttributeImpl (pr, at, e) -> "AttributeImpl("^pr^", "^at^", "^(reprOfLowExpr e)^")"