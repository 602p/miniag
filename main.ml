open Corelang

let someNTType : nonterminaltype = ("someNTType", ref [], ref [])

let setterProd : production = Production ("setter", someNTType, "top",
  [("x", StringT); ("e", BareNonterminalT someNTType)])
let addXProd : production = Production ("addX", someNTType, "top", [])

let downVal : attribute = Attribute ("downVal", StringT, Inh)
let upVal : attribute = Attribute ("upVal", StringT, Syn)

let addXupValRule : attrrule = (upVal, addXProd, SynImpl (
  BinOp (GetAttr (Name "top", downVal), Concat, Const (StringV "X"))))
(* let setterdownValRule : attrrule = (downVal, setterProd, InhImpl (1, Name "x")) *)
let setterupValRule : attrrule = (upVal, setterProd, SynImpl (GetAttr (Decorate (Name "e", [downVal, Name "x"]), upVal)))

let () = let (_, prods, attrs) = someNTType in
  prods := [setterProd; addXProd];
  attrs := [downVal; upVal]

let lang : language = Language (
  [someNTType],
  [],
  [downVal; upVal],
  [setterProd; addXProd],
  [addXupValRule; setterupValRule]
)

let tyCk, eval = getEval lang

(* let () = print_endline ([%show: language] lang) *)

let somev = BareNonterminalV (setterProd, [StringV "Foo"; BareNonterminalV (addXProd, [])])

let () = print_endline ([%show: value] somev)

let () = print_endline "\n\n"

let res = eval [] (GetAttr (Decorate (Const somev, []), upVal))

let () = print_endline ([%show: value] res)
