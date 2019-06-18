open Lang

let rec reprOfValue = function
	| StringV x -> "StringV(\"" ^ x ^ "\")"
	| IntV x -> "IntV(" ^ (string_of_int x) ^ ")"
	| BoolV true -> "BoolV(true)"
	| BoolV false -> "BoolV(false)"
	| UnitV -> "UnitV"
	| NonterminalV (_, _, _) -> "NonterminalV(...)"
	| TerminalV (_, _) -> "TerminalV(...)"