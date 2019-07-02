open Corelang
open Util

type lowstmt =
    | NonterminalDecl of lownt
                    (*   name *)
    | AttributeDecl of lowtype * lowattr * attrflowtype
                    (* type      name *)
    | AttributeAttach of lowattr * lownt
                    (*   attr     nonterminal *)
    | ProductionDecl of lowprod * (name * lownt) * (name * lowtype) list * lowrule list
                    (*  name      boundname nt      children and types *)
[@@ deriving show]
and lowrule = Rule of name * lowattr * lowexpr * string
[@@ deriving show]
and lowtype = name
and lownt = name
and lowattr = name
and lowprod = name
and lowexpr =
    | ConstInt of int
    | ConstBool of bool
    | ConstStr of string
    | BinOp of lowexpr * binoper * lowexpr
    | UnOp of lowexpr * unoper
    | IfThenElse of lowexpr * lowexpr * lowexpr
    | Construct of lowprod * lowexpr list
    | GetAttr of lowexpr * lowattr
    | Name of name
    | Decorate of lowexpr * (lowattr * lowexpr) list
[@@ deriving show]
and lowprog = lowstmt list

let rec raiseProg prog =
    print_endline " - Make ntMap...";
    let ntMap = List.fold_left
        (fun acc stmt -> match stmt with
            | NonterminalDecl name -> (name, (name, ref [], ref []))::acc
            | _ -> acc) [] prog in

    print_endline " - Make typeMap...";
    let typeMap = [("int", IntT); ("bool", BoolT); ("unit", UnitT); ("string", StringT)] @
                    (List.map (fun (name, x) -> (name, BareNonterminalT x)) ntMap) in

    print_endline " - Make attributeMap...";
    let attributeMap = List.fold_left
        (fun acc stmt -> match stmt with
            | AttributeDecl (ty, name, ft) -> (name, Attribute (name, assoc ty typeMap, ft))::acc
            | _ -> acc) [] prog in

    print_endline " - Make prodMap...";
    let prodMap = List.fold_left
        (fun acc stmt -> match stmt with
            | ProductionDecl (name, (boundname, ntname), children, _) ->
                (name, Production (name, assoc ntname ntMap, boundname,
                    List.map (fun (name, ty) -> (name, assoc ty typeMap)) children))::acc
            | _ -> acc) [] prog in

    print_endline " - associate attributes...";
    List.iter
        (fun stmt -> match stmt with
            | AttributeAttach (attrname, ntname) ->
                let attr = assoc attrname attributeMap in
                let nt = assoc ntname ntMap in
                let (_, _, attrs) = nt in
                attrs := attr::!attrs
            | _ -> ()) prog;

    print_endline " - Raise exprs for attributes...";
    let impls = flatMap (fun stmt -> match stmt with
        | ProductionDecl (prodname, (boundname, _), children, rules) ->
            let childnames = List.map fst children in
            List.map (fun rule -> match rule with Rule (name, attrname, body, comment) ->
                let attr = List.assoc attrname attributeMap in
                let prod = List.assoc prodname prodMap in
                (attr, prod,
                    (if name = boundname then SynImpl (raiseExpr prodMap attributeMap boundname childnames body)
                    else InhImpl ((findNth childnames name), (raiseExpr prodMap attributeMap boundname childnames body))),
                    comment
                )
            ) rules
        | _ -> []) prog in

    Language (
        List.map snd ntMap,
        [],
        List.map snd attributeMap,
        List.map snd prodMap,
        impls
    )

and raiseExpr prodmap attrmap parent children e = 
    let rec raiseExpr' x =
        match x with
        | ConstInt x -> Const (IntV x)
        | ConstBool x -> Const (BoolV x)
        | ConstStr x -> Const (StringV x)
        | BinOp (l, o, r) -> BinOp (raiseExpr' l, o, raiseExpr' r)
        | UnOp (a, o) -> UnOp (raiseExpr' a, o)
        | IfThenElse (i, t, e) -> IfThenElse (raiseExpr' i, raiseExpr' t, raiseExpr' e)
        | Construct (prodname, args) -> Construct (assoc prodname prodmap, List.map raiseExpr' args)
        | GetAttr (e, attrname) -> GetAttr (raiseExpr' e, assoc attrname attrmap)
        | Name x -> 
                    if x = parent then Self else
                    if List.mem x children then Child (findNth children x) else
                    Name x
        | Decorate (x, declist) -> Decorate (raiseExpr' x, List.map (fun x ->
            (List.assoc (fst x) attrmap, raiseExpr' (snd x))) declist)
    in raiseExpr' e