open Util

type typerep =
    | StringT
    | IntT
    | BoolT
    | UnitT
    | BareNonterminalT of nonterminaltype
    | DecoratedNonterminalT of nonterminaltype
    | TerminalT of terminaltype
[@@ deriving show { with_path = false }]

and nonterminaltype = ((name *
    (production [@printer fun fmt -> function Production (n, _, _, _) -> fprintf fmt "<P:%s>" n]) list ref *
    (attribute [@printer fun fmt -> function Attribute (n, _, _) -> fprintf fmt "<A:%s>" n]) list ref))
[@@ deriving show { with_path = false }]

and terminaltype = name
[@@ deriving show { with_path = false }]

and value =
    | StringV of string
    | IntV of int
    | BoolV of bool
    | UnitV
    | BareNonterminalV of (production [@printer fun fmt -> function Production (n, (b, _, _), _, _) -> fprintf fmt "<P:%s (%s)>" n b]) *
        value list * origininfo
    | DecoratedNonterminalV of (production [@printer fun fmt -> function Production (n, (b, _, _), _, _) -> fprintf fmt "<P:%s (%s)>" n b]) *
        value list * attrinst list * value * origininfo
    | TerminalV of terminaltype * string
[@@ deriving show { with_path = false }]

and attrinst =
    | InhI of ((evalctx [@opaque]) * lzexp) option
    | SynI of lzexp
[@@ deriving show { with_path = false }]

and production = Production of name
    * nonterminaltype (* type of produced nonterminal (i.e. what this prod belongs to) *)
    * name (* name bound to the production *)
    * (name * typerep) list (* name and type of children *)
[@@ deriving show { with_path = false }]

and attrflowtype = Inh | Syn
[@@ deriving show { with_path = false }]

and attribute = Attribute of name * typerep * attrflowtype
[@@ deriving show { with_path = false }]

and expr =
    | Const of value
    | BinOp of expr * binoper * expr
    | UnOp of expr * unoper
    | Let of expr * string * expr
    | Name of string
    | IfThenElse of expr * expr * expr

    | Self
    | Child of int

    | Construct of production * expr list
    | GetAttr of expr * attribute
    | Decorate of expr * (attribute * expr) list
    | New of expr
[@@ deriving show { with_path = false }]

and binoper = Add | Sub | Mul | Div | Concat | Eq
[@@ deriving show { with_path = false }]

and unoper = Not | Neg
[@@ deriving show { with_path = false }]

and 'a env = (name * 'a) list
[@@ deriving show { with_path = false }]

and name = string
[@@ deriving show { with_path = false }]

and attrrule = attribute * production * attrimpl * string
[@@ deriving show { with_path = false }]

and attrimpl =
    | InhImpl of int * (* child number *)
                expr (* expr in scope of 'Self' *)
    | SynImpl of expr (* expr in scope of node *)
[@@ deriving show { with_path = false }]

and language = Language of
    nonterminaltype list *
    terminaltype list *
    attribute list *
    production list *
    attrrule list
[@@ deriving show { with_path = false }]

and lzexp = lzexpinner ref
[@@ deriving show { with_path = false }]

and lzexpinner =
    | Waiting of bool ref * value env * attrrule option * expr
                 (* bool = inprogress *)
    | Forced of value * attrrule option
[@@ deriving show { with_path = false }]

and evalctx = (value * attrrule option) option
    (* nt-owning-the-rule-being-evaluated or None=toplevel *)
[@@ deriving show { with_path = false }]

and origininfo =
    value option * bool * value option * string
[@printer fun fmt _ -> fprintf fmt "<OI>"]
[@@ deriving show { with_path = false }]


let nameOfAttr = function Attribute (n, _, _) -> n
let prodOfNt = function
    | BareNonterminalV (p, _, _) -> p
    | DecoratedNonterminalV (p, _, _, _, _) -> p
    | _ -> failwith "prodOfNt not of NT"

let getChildByName v n = match v with
    | BareNonterminalV (Production (_, _, _, childmap), children, _) ->
        List.nth children (findNthP childmap (fun x -> (fst x) = n))
    | DecoratedNonterminalV (Production (_, _, _, childmap), children, _, _, _) ->
        List.nth children (findNthP childmap (fun x -> (fst x) = n))
    | _ -> failwith "getChildByName not of *NonterminalV"

let getAttrSlotByName v n = match v with
    | DecoratedNonterminalV (Production (_, (_, _, attrmap), _, _), _, attrs, _, _) ->
        List.nth attrs (findNthI !attrmap n)
    | _ -> failwith "getAttrSlotByName not of DecoratedNonterminalV"

let typeEq x y = match x, y with
    | BareNonterminalT (xname, _, _), BareNonterminalT (yname, _, _) -> xname = yname
    | DecoratedNonterminalT (xname, _, _), DecoratedNonterminalT (yname, _, _) -> xname = yname
    | x, y -> x = y

let setRule r = function
    | None -> None
    | Some (x, _) -> Some (x, r)

let getRule = function
    | None -> None
    | Some (_, r) -> r

let attrEq x y = x == y
let prodEq x y = x == y

let typeOfValue : value -> typerep = function
    | StringV _ -> StringT
    | IntV _ -> IntT
    | BoolV _ -> BoolT
    | UnitV -> UnitT
    | BareNonterminalV (Production(_, ty, _, _), _, _) -> BareNonterminalT ty
    | DecoratedNonterminalV (Production(_, ty, _, _), _, _, _, _) -> DecoratedNonterminalT ty
    | TerminalV (ty, _) -> TerminalT ty

let extractOrigin = function
    | Some (DecoratedNonterminalV (_, _, _, v, _), _) -> Some v
    | Some (x, _) -> Some x
    | None -> None

let getLabel = function
    | Some (_, Some (_, _, _, l)) -> l
    | _ -> ""

let getEval lang =
    match lang with Language (_, _, _, _, rules) ->
    let rec evalExpr (ctx : evalctx) (env : value env) (expr : expr) : value =
        (* print_endline ("eval: "^([%show: expr] expr)^"\n <<"); *)
        let evalExpr' = evalExpr ctx in
        let r = (match expr with
        | Const v -> v
        | BinOp (l, op, r) ->
            let l', r' = evalExpr' env l, evalExpr' env r in
            (
            let do_iii op = (match l', r' with
                | IntV l'', IntV r'' -> IntV (op l'' r'')
                | _ -> failwith "bad actual type to int binop") in
            match op with
            | Add -> do_iii (+)
            | Sub -> do_iii (-)
            | Mul -> do_iii ( * )
            | Div -> do_iii (/)
            | Concat -> (match l', r' with
                | StringV l'', StringV r'' -> StringV (l'' ^ r'')
                | _ -> failwith "bad actual type to string binop")
            | Eq -> (match l', r' with
                | StringV l'', StringV r'' -> BoolV (l'' = r'')
                | BoolV l'', BoolV r'' -> BoolV (l'' = r'')
                | IntV l'', IntV r'' -> BoolV (l'' = r'')
                | UnitV, UnitV -> BoolV true
                | _ -> failwith "bad actual type to bool binop"))
        | UnOp (a, op) ->
            let a' = evalExpr' env a in
            (match op with
            | Not -> (match a' with
                | BoolV a'' -> BoolV (not a'')
                | _ -> failwith "bad actual type to bool unop")
            | Neg -> (match a' with
                | IntV a'' -> IntV (-a'')
                | _ -> failwith "bad actual type to int unop"))
        | Let (bound, binding, body) -> evalExpr' ((binding, evalExpr' env bound)::env) body
        | Name x -> List.assoc x env
        | IfThenElse (cond, t, f) -> (match evalExpr' env cond with
            | BoolV true -> evalExpr' env t
            | BoolV false -> evalExpr' env f
            | _ -> failwith "bad actual type to ifthenelse")

        (* ------------------------------------------------------------------- *)

        | Self -> fst (assertSome ctx)
        | Child x -> (match fst (assertSome ctx) with
            | DecoratedNonterminalV (_, children, _, _, _) -> List.nth children x
            | BareNonterminalV (_, children, _) -> List.nth children x
            | _ -> failwith "CTX not NT?")

        (* ------------------------------------------------------------------- *)

        | Construct (prod, args) ->
            (let args = List.map (evalExpr' env) args in
            match prod with Production (name, _, _, childrentys) ->
            enforce (List.length args = List.length childrentys) "bad actual nr args to a Construct";
            List.iter2 (fun x y -> enforce (typeEq (typeOfValue x) (snd y))
                ("bad actual type to a Construct("^name^"): "^([%show:typerep] (typeOfValue x)))) args childrentys;
            BareNonterminalV (prod, args, (extractOrigin ctx, false, None, getLabel ctx)))

        | GetAttr (nt, attr) ->
            (match evalExpr' env nt with
                | DecoratedNonterminalV _ as v -> resolveAttr v ctx attr
                | BareNonterminalV _ as v -> resolveAttr (doAutoDec ctx env v) ctx attr
                | _ -> failwith "bad actual type to GetAttr")

        | Decorate (e, b) ->
            makeDecNT ctx (evalExpr' env e) env (List.map (fun x -> fst x, (snd x, None)) b)

        | New x ->
            duplicate ctx (evalExpr' env x)
        ) in 
            (* print_endline ">>"; *)
            r

    and makeDecNT ctx nt env (bindings : (attribute * (expr * attrrule option)) list) = match nt with
        | BareNonterminalV (Production (_, (_, _, attrmap), _, _) as prod, children, origoi) as bare->
            let attrs = List.map (fun attr -> match List.assoc_opt attr bindings with
                | Some (v, r) -> InhI (Some (ctx, makeLzExp env r v))
                | None -> applyFirst (function
                        | (attr', prod', SynImpl e, _) as rule when (attrEq attr' attr) && (prodEq prod' prod) ->
                            Some (SynI (makeLzExp env (Some rule) e))
                        | _ -> None) (InhI None) rules
            ) !attrmap in DecoratedNonterminalV (prod, children, attrs, nt,
                (None, false, None, "DECORATED DUMMY"))
        | _ -> failwith "bad args to makeDecNT"

    and makeLzExp env r expr =
        ref (Waiting (ref false, env, r, expr))

    and forceLzExp ctx lzexp = match !lzexp with
        | Forced (x, _) -> x
        | Waiting (inprogress, env, r, expr) ->
            if !inprogress then
                (print_endline "\n---CIRCULAR FORCING---";
                print_endline ([%show:lzexp] lzexp);
                print_endline ([%show:evalctx] ctx);
                failwith "Circular forcing")
            else
            inprogress := true;
            let res = evalExpr (setRule r ctx) env expr in
            lzexp := Forced (res, r); res

    and resolveAttr v ctx attr = match (getAttrSlotByName v attr), ctx with
        | InhI (Some(ctx, f)), _ -> forceLzExp ctx f
        | SynI f, Some (_, r) -> forceLzExp (Some (v, r)) f
        | SynI f, None -> forceLzExp (Some (v, None)) f
        | InhI (None), _ -> failwith "inh attribute not provided"

    and doAutoDec ctx env v = 
        match ctx with
        | Some (DecoratedNonterminalV (_, ctxchildren, _, _, _) as ctxv, _) ->
            let validrules = filterMap (fun rule -> match rule with
                | (attr, ruleprod, InhImpl (childno, expr), _) when (prodEq ruleprod (prodOfNt ctxv) && 
                    (List.nth ctxchildren childno) == v) -> Some (attr, (expr, Some rule))
                | _ -> None
            ) rules
            in
                makeDecNT ctx v env validrules
        | _ -> failwith "doAutoDec with no ctx"

    and duplicate ctx x = 
        let r = getRule ctx in
        let dup' = duplicate ctx in
        match x with
            | BareNonterminalV (p, v, _) as h -> BareNonterminalV (p, List.map dup' v, (Some h, false, None, getLabel ctx))
            | DecoratedNonterminalV (p, v, _, o, _) as h -> BareNonterminalV (p, List.map dup' v, (Some o, false, None, getLabel ctx))
            (* | IntV x -> IntV x
            | StringV x -> StringV x
            | BoolV x -> BoolV x *)
            | x -> x

    in evalExpr None []