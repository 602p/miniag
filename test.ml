#use "core.ml"

let rec simplent = ("simplent", ref [simplentprod], ref [resattr])
and simplenttype = NonterminalT simplent
and resattr = Attribute ("res", simplent, IntT)
and resattrimpl = BinOp (Name "x", Add, Name "y")
and simplentprod = Production ("simplentprod", simplent, [("x", IntT); ("y", IntT)], [(resattr, resattrimpl)])

let e = BinOp (Const (IntV 3), Add, Const (IntV 2))
let et = tyCkExpr [] e
let ev = evalExpr [] e

let e2 = Construct (simplentprod, [Const (IntV 3); Const (IntV 7)])
let e2t = tyCkExpr [] e2
let e2v = evalExpr [] e2
let r = evalExpr [] (GetAttr (e2, resattr))