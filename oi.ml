open Corelang
open Util

let getoi = function
    | BareNonterminalV (_, _, oi)
    | DecoratedNonterminalV (_, _, _, _, oi) ->
        Some oi
    | _ -> None

let rec actually_pretty_print = function
    | BareNonterminalV (Production (p, _, _, _), values, _) ->
        p^"("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | DecoratedNonterminalV (Production (p, _, _, _), values, _, _, _) ->
        p^"*("^(stringJoin ", " (List.map actually_pretty_print values))^")"
    | x -> "^"^([%show:value] x)

let getComment = function (_, _, _, c) -> c

let rec string_of_oi = function
    | None, _, _, _ -> "None"
    | Some x, isContractum, redex, label -> "Some "^"\n -- linked rule: "^
        "#"^label
        ^"\n\n -- linked value: "^(actually_pretty_print x)^(match x with
        | BareNonterminalV(_, _, oi)
        | DecoratedNonterminalV(_, _, _, _, oi) ->
            "\n -> "^(string_of_oi oi)
        | _ -> "\n -> X")

let rec debug_oi res = match res with
  | BareNonterminalV(_, children, oi)
  | DecoratedNonterminalV(_, children, _, _, oi) ->
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

let rec assoc_opt_id n = function
    | [] -> None
    | (x,v)::_ when x==n -> Some v
    | _::xs -> assoc_opt_id n xs

let makeGraphViz (thing : value) =
    let oc = open_out "out/oi.dot" in
    let print_endline x = output_string oc (x^"\n") in
    let print_string = output_string oc in
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
    let rec emit (x : value) : string = if isDone x then makeOrGet x else
        let name = makeOrGet x in
        let label = match x with
        | BareNonterminalV (Production (p, _, _, _), _, _) -> p
        | DecoratedNonterminalV (Production (p, _, _, _), _, _, _, _) -> p^"*"
        | StringV v -> "\\\""^v^"\\\""
        | _ -> [%show: value] x
        in
        print_string (name^" [label=\""^label^"\" ");
        if x == thing then print_string "color=red";
        print_endline "];";
        (match x with
        | BareNonterminalV (Production (_, _, _, childnames), children, oi)
        | DecoratedNonterminalV (Production (_, _, _, childnames), children, _, _, oi) ->
            List.iter2 (fun binding ch -> print_endline (name^" -> "^(emit ch)^" [label=\""^(fst binding)^"\"];")) childnames children;
            (match oi with
                | Some x, _, _, r -> 
                    (* let x = match x with
                        | DecoratedNonterminalV (_, _, _, _, (Some(x, _), _)) -> x
                        | x -> x in *)
                    print_endline ((name)^" -> "^(emit x)^" [style=dashed label=\""^r^"\"];")
                | _ -> ())
        | _ -> ());
        (match x with
            | DecoratedNonterminalV (Production (_, (_, _, attrs), _, _), _, attrimpls, _, _) ->
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
    print_endline "}";
    close_out oc;
    ignore (Sys.command "dot -Tpng out/oi.dot -o out/oi.png")