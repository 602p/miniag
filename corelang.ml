open Util

type typerep =
    | StringT
    | IntT
    | BoolT
    | UnitT
    | NonterminalT of nonterminaltype
    | TerminalT of terminaltype
    | TyVarT of string
[@@ deriving show { with_path = false }]
and nonterminaltype = ((name *
    production list ref *
    attribute list ref)
[@printer fun fmt (x, _, _) -> fprintf fmt "<%s>" x])
[@@ deriving show { with_path = false }]
and terminaltype = name
[@@ deriving show { with_path = false }]
and value =
    | StringV of string
    | IntV of int
    | BoolV of bool
    | UnitV
    | NonterminalV of production * value list * value option ref list
                     (* prod      children      attr values (prod ordered) *)
    | TerminalV of terminaltype * string
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
    | Construct of production * expr list
    | GetAttr of expr * attribute
[@@ deriving show { with_path = false }]
and binoper = Add | Sub | Mul | Div | Concat | Eq
[@@ deriving show { with_path = false }]
and unoper = Not | Neg
[@@ deriving show { with_path = false }]
and 'a env = (name * 'a) list
[@@ deriving show { with_path = false }]
and name = string
[@@ deriving show { with_path = false }]
and attrrule = attribute * production * attrimpl
[@@ deriving show { with_path = false }]
and attrimpl =
    | InhImpl of int * (* child number *)
                expr (* expr in scope of 'parent' *)
    | SynImpl of expr (* expr in scope of node *)
[@@ deriving show { with_path = false }]
and language = Language of
    nonterminaltype list *
    terminaltype list *
    attribute list *
    production list *
    attrrule list
[@@ deriving show { with_path = false }]

let nameOfAttr = function Attribute (n, _, _) -> n

let getChildByName v n = match v with
    | NonterminalV (Production (_, _, _, childmap), children, _) ->
        List.nth children (findNthP childmap (fun x -> (fst x) = n))
    | _ -> failwith "getChildByName not of NonterminalV"

let getAttrSlotByName v n = match v with
    | NonterminalV (Production (_, (_, _, attrmap), _, _), _, attrs) ->
        List.nth attrs (findNth !attrmap n)
    | _ -> failwith "getAttrSlotByName not of NonterminalV"

let typeEq x y = match x, y with
    | NonterminalT (xname, _, _), NonterminalT (yname, _, _) -> xname = yname
    | x, y -> x = y

let typeOfValue : value -> typerep = function
    | StringV _ -> StringT
    | IntV _ -> IntT
    | BoolV _ -> BoolT
    | UnitV -> UnitT
    | NonterminalV (Production(_, ty, _, _), _, _) -> NonterminalT ty
    | TerminalV (ty, _) -> TerminalT ty

let rec tyCkExpr (env : typerep env) (expr : expr) : typerep = match expr with
    | Const v -> typeOfValue v
    | BinOp (l, op, r) -> (match op with
        |Eq -> enforce ((tyCkExpr env l) = (tyCkExpr env r)) "invalid args to eq"; BoolT
        | _ ->
            let correctL, correctR, res = match op with
                | Add | Sub | Mul | Div -> IntT, IntT, IntT
                | Concat -> StringT, StringT, StringT
                | _ -> failwith "!?"
            in
                enforce (tyCkExpr env l = correctL) "invalid lhs type in binop";
                enforce (tyCkExpr env r = correctR) "invalid rhs type in binop";
                res)
    | UnOp (a, op) -> let correctA, res = match op with
            | Not -> BoolT, BoolT
            | Neg -> IntT, IntT
        in
            enforce (tyCkExpr env a = correctA) "invalid expr type in unop";
            res
    | Let (bound, binding, body) -> tyCkExpr ((binding, tyCkExpr env bound)::env) body
    | Name x -> List.assoc x env
    | IfThenElse (cond, t, f) ->
        enforce (tyCkExpr env cond = BoolT) "invalid cond type in ifthenelse";
        let tty = tyCkExpr env t in
        enforce (tty = tyCkExpr env f) "arms not same type in ifthenelse";
        tty
    | Construct (prod, args) ->
        (let argtys = List.map (tyCkExpr env) args in
        match prod with Production (name, res, _, reqtys) ->
        enforce (List.length argtys = List.length reqtys) "bad nr args to a Construct";
        List.iter2 (fun x y -> enforce (x = (snd y)) "bad type to a Construct") argtys reqtys;
        NonterminalT res)
    | GetAttr (nt, attr) ->
        (* (match tyCkExpr env nt with NonterminalV (prod, children, thunks) ->
        enforce (List.mem attr )) *)
        match attr with Attribute (_, ty, _) -> ty

let rec evalExpr (env : value env) (expr : expr) : value =
    match expr with
    | Const v -> v
    | BinOp (l, op, r) ->
        let l', r' = evalExpr env l, evalExpr env r in
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
        let a' = evalExpr env a in
        (match op with
        | Not -> (match a' with
            | BoolV a'' -> BoolV (not a'')
            | _ -> failwith "bad actual type to bool unop")
        | Neg -> (match a' with
            | IntV a'' -> IntV (-a'')
            | _ -> failwith "bad actual type to int unop"))
    | Let (bound, binding, body) -> evalExpr ((binding, evalExpr env bound)::env) body
    | Name x -> List.assoc x env
    | IfThenElse (cond, t, f) -> (match evalExpr env cond with
        | BoolV true -> evalExpr env t
        | BoolV false -> evalExpr env f
        | _ -> failwith "bad actual type to ifthenelse")
    | Construct (prod, args) ->
        (let args = List.map (evalExpr env) args in
        match prod with Production (name, (_, _, attrs), _, childrentys) ->
        enforce (List.length args = List.length childrentys) "bad actual nr args to a Construct";
        List.iter2 (fun x y -> enforce (typeEq (typeOfValue x) (snd y)) ("bad actual type to a Construct("^name^")")) args childrentys;
       NonterminalV (prod, args, List.map (fun _ -> ref None) !attrs))
    | GetAttr (nt, attr) ->
        match evalExpr env nt with
            | NonterminalV (Production (_, (_, _, attrs), _, _), children, thunks) as v ->
                (match !(getAttrSlotByName v attr) with
                    | Some x -> x
                    | None -> failwith "asidasdi")
            | _ -> failwith "bad actual type to GetAttr"

