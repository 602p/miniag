open Corelang
open Util

type lowstmt =
    | NonterminalDecl of lownt
                    (*   name *)
    | AttributeDecl of lowtype * lowattr
                    (* type      name *)
    | AttributeAttach of lowattr * lownt
                    (*   attr     nonterminal *)
    | ProductionDecl of lowprod * (name * lownt) * (name * lowtype) list
                    (*  name      boundname nt      children and types *)
    | AttributeImpl of lowprod * lowattr * lowexpr
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
and lowprog = lowstmt list

let rec raiseProg prog =
    print_endline " - Make ntMap...";
    let ntMap = List.fold_left
        (fun acc stmt -> match stmt with
            | NonterminalDecl name -> (name, (name, ref [], ref []))::acc
            | _ -> acc) [] prog in
    print_endline " - Make typeMap...";
    let typeMap = [("int", IntT); ("bool", BoolT); ("unit", UnitT); ("string", StringT)] @
                    (List.map (fun (name, x) -> (name, NonterminalT x)) ntMap) in
    print_endline " - Make attributeMap...";
    let attributeMap = List.fold_left
        (fun acc stmt -> match stmt with
            | AttributeDecl (ty, name) -> (name, Attribute (name, assoc ty typeMap))::acc
            | _ -> acc) [] prog in
    print_endline " - Make prodMap...";
    let prodMap = List.fold_left
        (fun acc stmt -> match stmt with
            | ProductionDecl (name, (boundname, ntname), children) ->
                (name, Production (name, assoc ntname ntMap, "",
                    List.map (fun (name, ty) -> (name, assoc ty typeMap)) children, ref []))::acc
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
    List.iter (fun stmt -> match stmt with
        | AttributeImpl (prodname, attrname, lowexpr) ->
            (match assoc prodname prodMap with Production (name, ntname, _, children, attrs) ->
            let attr = assoc attrname attributeMap in
            attrs := (attr, raiseExpr prodMap attributeMap lowexpr)::!attrs)
        | _ -> ()) prog;
    prodMap, attributeMap
and raiseExpr prodmap attrmap e = 
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
        | Name x -> Name x
    in raiseExpr' e