open Corelang
open Util

let rec actually_pretty_print = function
    | BareNonterminalV (Production (p, _, _, _), values, _) ->
        p^"("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | DecoratedNonterminalV (Production (p, _, _, _), values, _, _) ->
        p^"*("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | IntV x -> string_of_int x
    | StringV x -> "\\\""^x^"\\\""
    | x -> "^"^([%show:value] x)

let is_primitive = function
    | StringV _ -> true
    | IntV _ -> true
    | BoolV _ -> true
    | UnitV -> true
    | _ -> false

let getoi = function
    | BareNonterminalV (_, _, oi)
    | DecoratedNonterminalV (_, _, _, BareNonterminalV(_, _, oi)) ->
        Some oi
    | _ -> None

let hasoi = function
    | BareNonterminalV (_, _, oi)
    | DecoratedNonterminalV (_, _, _, BareNonterminalV(_, _, oi)) ->
        true
    | _ -> false

let nodebody_pp = function
    | BareNonterminalV (Production (p, _, _, _), values, _) ->
        if values = [] then
            p
        else if listAll is_primitive values then 
            p^"("^(stringJoin ", " (List.map actually_pretty_print values))^")"
        else
            p
    | x -> actually_pretty_print x

let willBeOneNode = function
    | BareNonterminalV(_, v, _) -> listAll is_primitive v
    | _ -> true

let rec assoc_opt_id n = function
    | [] -> None
    | (x,v)::_ when x==n -> Some v
    | _::xs -> assoc_opt_id n xs

let rec mem_id n = function
    | [] -> false
    | x::xs -> x==n || mem_id n xs

let rec backslash l1 l2 = match l1 with
    | [] -> []
    | x::xs -> if mem_id x l2 then backslash xs l2 else x::(backslash xs l2)

let rec findAllChildren = function
    | BareNonterminalV(_, v, _) as x -> v @ flatMap findAllChildren v
    | x -> [x]

let rec findParent (pool : value list) (child : value) : value option =
    let rec findParentOne child obj =
        match obj with
        | BareNonterminalV(_, v, _) as x ->
            if mem_id child v then Some x else applyFirstOpt (findParentOne child) v
        | _ -> None in
    applyFirstOpt (findParentOne child) pool

let isOwnedByAny xs x = listAny (fun l -> x!=l && mem_id x (findAllChildren l)) xs

let append x v = x := v::!x

let getRedexAttrOpt = function
    | Some (BareNonterminalV (_, _, (_, _, r, _))) -> r
    | _ -> None

let makeGraphViz (root : value) =
    let oc = open_out "out/oi.dot" in
    let emit_endline x = output_string oc (x^"\n") in
    let emit_string = output_string oc in
    let names : (value * string) list ref = ref [] in
    let currname = ref 0 in
    let getNewName () =
        let curr = !currname in
        currname := curr + 1;
        "n"^(string_of_int curr) in
    let makeOrGet v = match assoc_opt_id v !names with
        | None -> let newname = getNewName () in
            names := (v, newname)::!names; newname
        | Some x -> x in
    let isDone x = let f = assoc_opt_id x (!names) in
        match f with Some _ -> true | None -> false in

    let objectsToEmit = ref [] in
    let seenObjects = ref [root] in
    let objectsEmitted = ref [root] in

    let rec emitObjectWithoutLinks isAnswer x : unit = let x = shuckValue x in if isDone x then () else
        let name = makeOrGet x in
        append seenObjects x;
        append objectsEmitted x;
        let pushTodo x = (append objectsToEmit x; append seenObjects x) in
        emit_string (name ^ "[label=\"" ^ (nodebody_pp x) ^ "\" ");
        (if x == root then emit_string " color=blue ");
        (if isAnswer then emit_string " fillcolor=\"#bbbbff\" style=filled ");
        (if hasoi x then
            let (origin, isContractum, redex, originLabel) = assertSome (getoi x) in
            (match origin with
            | Some x ->
                if isMain x then emit_string " fillcolor=\"#ffbbbb\" style=filled "
                else (
                    (match redex with
                    | Some (r, _) -> pushTodo r
                    | _ -> ());
                    (if isContractum then emit_string " shape=diamond ");
                pushTodo x);
            | _ -> ()));
        emit_endline "];";
        (if not (willBeOneNode x) then
            (emit_endline ("subgraph children"^(getNewName ())^"{\n");
            (match x with
            | BareNonterminalV(Production(_, _, _, childnames), children, _) ->
                List.iter2 (fun binding ch ->
                    emitObjectWithoutLinks isAnswer ch;
                    append seenObjects ch;
                    emit_endline (name^" -> "^(makeOrGet ch)
                        ^" [arrowhead=none taillabel=\""^(fst binding)^"\"];")) childnames children
            | _ -> ());
            emit_endline "}")) in

    emit_endline "digraph {";
    emit_endline "node [fontname = \"monospace\"];";
    emit_endline "graph [compound=true";
    emit_endline "rankdir=TB";
    emit_endline "];";
    emit_endline "subgraph { ";
    emit_endline "subgraph clusterROOT{";
    emitObjectWithoutLinks true root;
    emit_endline "}";
    while !objectsToEmit != [] do
        let todo = List.find (negatep (isOwnedByAny !objectsToEmit)) !objectsToEmit in
        emit_endline ("subgraph cluster"^(getNewName ())^"{");
        ignore (emitObjectWithoutLinks false todo);
        emit_endline "}";
        append objectsEmitted todo;
        objectsToEmit := backslash !objectsToEmit !objectsEmitted;
    done;

    let parent = findParent !seenObjects in
    let rec getRedex (t : value option) : (value * string) option =
        if t = None then None
        else (if getRedexAttrOpt t != None then getRedexAttrOpt t
            else getRedex (parent (assertSome t))) in
    let rec getContractum (t : value option) : value option =
        if t = None then None
        else (if getRedexAttrOpt t != None then t
            else getContractum (parent (assertSome t))) in

    let emitOriginInfo x =
        let name = makeOrGet x in
        print_endline ((actually_pretty_print x)^" -- "^(string_of_bool (hasoi x)));
        if hasoi x then 
            (let (origin, isContractum, redex, originLabel) = assertSome (getoi x) in
            (match origin with
                | Some x -> if not (isMain x) then
                    emit_endline (name ^ "->" ^ (makeOrGet x) ^ "[style=dashed label=\""^originLabel^"\"];")
                | None -> ());
            (match getRedex (Some x) with
                | Some (x, c) -> if not (isMain x) then
                    emit_endline (name ^ "->" ^ (makeOrGet x) ^ "[style=dotted label=\""^c^"\"];")
                | None -> ());
            (match getContractum (Some x) with
                | Some x -> if not (isMain x) then
                    emit_endline (name ^ "->" ^ (makeOrGet x) ^ "[style=dotted penwidth=3 ];")
                | None -> ())) in

    objectsToEmit := !seenObjects;
    objectsEmitted := [];
    print_endline ([%show: int] (List.length !objectsToEmit));
    while !objectsToEmit != [] do
        let todo = List.hd !objectsToEmit in
        ignore (emitOriginInfo todo);
        append objectsEmitted todo;
        objectsToEmit := backslash !objectsToEmit !objectsEmitted;
    done;

    emit_endline "}}";
    close_out oc;
    ignore (Sys.command "bash draw.sh")