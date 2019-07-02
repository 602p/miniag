open Corelang
open Util

let getoi = function
    | BareNonterminalV (_, _, oi)
    | DecoratedNonterminalV (_, _, _, oi) ->
        Some oi
    | _ -> None

let rec actually_pretty_print = function
    | BareNonterminalV (Production (p, _, _, _), values, _) ->
        p^"("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | DecoratedNonterminalV (Production (p, _, _, _), values, _, _) ->
        p^"*("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | x -> "^"^([%show:value] x)

let getComment = function (_, _, _, c) -> c

let rec string_of_oi = function
    | None, _ -> "None"
    | Some (x, r), s -> "Some -- "^s^"\n -- linked rule: "^
        (match r with
            | None -> "None"
            | Some r -> "#"^(getComment r))
        ^"\n\n -- linked value: "^(actually_pretty_print x)^(match x with
        | BareNonterminalV(_, _, oi)
        | DecoratedNonterminalV(_, _, _, oi) ->
            "\n -> "^(string_of_oi oi)
        | _ -> "\n -> X")

let rec debug_oi res = match res with
  | BareNonterminalV(_, children, oi)
  | DecoratedNonterminalV(_, children, _, oi) ->
    List.iter (fun x ->
      match (getoi x) with 
        | None -> ()
        | Some oi -> (
          print_endline ("\n\nOI for "^(actually_pretty_print x)^":");
          print_endline (string_of_oi oi));
          debug_oi x) (children)
  | _ -> ()

let getOriginValue = function
    | Some (x, _), _ -> Some x
    | None, _ -> None


let makeGraphViz (thing : value) =
    let names : (value * string) list ref = ref [] in
    let currname = ref 0 in
    let getNewName () =
        let curr = !currname in
        currname := curr + 1;
        "n"^(string_of_int curr) in
    let makeOrGet v = match List.assoc_opt v !names with
        | None -> let newname = getNewName () in
            names := (v, newname)::!names; newname
        | Some x -> x in
    let isDone x = match List.assoc_opt x (!names) with Some _ -> true | None -> false in
    let rec emit (x : value) : string = if isDone x then makeOrGet x else
        let name = makeOrGet x in
        let label = match x with
        | BareNonterminalV (Production (p, _, _, _), _, _) -> p
        | DecoratedNonterminalV (Production (p, _, _, _), _, _, _) -> p^"*"
        | _ -> [%show: value] x
        in
        print_string (name^" [label=\""^label^"\" ");
        if x == thing then print_string "color=red";
        print_endline "];";
        (match x with
        | BareNonterminalV (Production (_, _, _, childnames), children, oi)
        | DecoratedNonterminalV (Production (_, _, _, childnames), children, _, oi) ->
            List.iter2 (fun binding ch -> print_endline (name^" -> "^(emit ch)^" [label=\""^(fst binding)^"\"];")) childnames children;
            (match oi with
                | Some (x, r), _ -> print_string ((name)^" -> "^(emit x)^" [style=dashed ");
                    (match r with
                    | Some (_, _, _, c) -> print_string ("label=\""^c^"\"")
                    | None -> ());
                    print_endline "];"
                | None, _ -> ())
        | _ -> ());
        (match x with
            | DecoratedNonterminalV (Production (_, (_, _, attrs), _, _), _, attrimpls, _) ->
                List.iter2 (fun a ai ->
                    match a, (match ai with
                    | InhI (Some (_, lzz)) -> (match !lzz with
                        | Forced (v, _) -> Some v
                        | _ -> None)
                    | InhI None -> None
                    | SynI lzz -> (match !lzz with
                        | Forced (v, _) -> Some v
                        | _ -> None)) with
                    | Attribute (n, _, _), Some v -> 
                        print_endline ((emit x)^" -> "^(emit v)^" [style=dotted label=\""^n^"\"];")
                    | _, None -> ()
                ) !attrs attrimpls
            | _ -> ());
        name
    in
    print_endline "digraph {";
    ignore (emit thing);
    print_endline "}"