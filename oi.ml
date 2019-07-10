open Corelang
open Util

let getoi = function
    | BareNonterminalV (_, _, oi)
    | DecoratedNonterminalV (_, _, _, BareNonterminalV(_, _, oi)) ->
        Some oi
    | _ -> None

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

let nodebody_pp = function
    | BareNonterminalV (Production (p, _, _, _), values, _) ->
        if values = [] then
            p
        else if listAll is_primitive values then 
            p^"("^(stringJoin ", " (List.map actually_pretty_print values))^")"
        else
            p
    | x -> actually_pretty_print x

let getComment = function (_, _, _, c) -> c

let rec string_of_oi = function
    | None, _, _, _ -> "None"
    | Some x, isContractum, redex, label -> "Some "
        ^"isContractum = "^(string_of_bool isContractum)
        ^"\n -- redex: "^ (match redex with
            | Some (r, c) -> "Some "^(actually_pretty_print r)^": "^c
            | _ -> "None")
        ^"\n -- linked rule: "^
        "#"^label
        ^"\n\n -- linked value: "^(actually_pretty_print x)^(match x with
        | BareNonterminalV(_, _, _)
        | DecoratedNonterminalV(_, _, _, _) as v ->
            "\n -> "^(string_of_oi (assertSome (getoi v)))
        | _ -> "\n -> X")

let rec debug_oi res = match res with
  | BareNonterminalV(_, children, _)
  | DecoratedNonterminalV(_, children, _, _) ->
    let oi = assertSome (getoi res) in
    List.iter (fun x ->
      match (getoi x) with 
        | None -> ()
        | Some oi -> (
          print_endline ("\n\nOI for "^(actually_pretty_print x)^":");
          print_endline (string_of_oi oi));
          debug_oi x) (children)
  | _ -> ()

let rec assoc_opt_id n = function
    | [] -> None
    | (x,v)::_ when x==n -> Some v
    | _::xs -> assoc_opt_id n xs

let makeGraphViz (thing : value) =
    print_endline ("\n\nEMITROOT\n"^([%show:value] thing)); 
    print_endline ("\nHASH="^(string_of_int (Hashtbl.hash thing)));
    print_endline (string_of_oi (assertSome (getoi thing))); debug_oi thing;
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
    let rec emit (isResult : bool) (parentRedex : (value*string) option) (parentContractum : value option) (x : value) : string =
        let emit' = emit false None None in
        let redex = ref None in
        let drewContractum = ref false in
        (if isDone x then () else
        let name = makeOrGet x in
        let label = nodebody_pp x in
        let isContractum = ref false in
        let isConstructedInMain = ref false in
        (match x with
        | BareNonterminalV (Production (_, _, _, childnames), children, _)
        | DecoratedNonterminalV (Production (_, _, _, childnames), children, _, _) ->
            let oi = assertSome (getoi x) in
            let myredex = match oi with | _, _, r, _ -> r in
            let mycontractum = match myredex with
                | Some (r, _) ->
                    if not (isMain r) then
                        (print_endline (name ^" -> " ^ name ^"[style=dotted penwidth=3];"); drewContractum := true; Some x)
                    else parentContractum
                | None -> parentContractum in
            let myredex = match myredex with
                | None -> parentRedex
                | x -> x in
            (if listAll is_primitive children then () else 
            List.iter2 (fun binding ch -> print_endline (name^" -> "^(emit isResult myredex mycontractum ch)^" [arrowhead=none taillabel=\""^(fst binding)^"\"];")) childnames children);
            (match oi with
                | Some x, isContractum', redex', r -> 
                    (if isMain x then isConstructedInMain := true else 
                    (print_string ((name)^" -> "^(emit' x)^" [style=dashed label=\""^r^"\"");
                    isContractum := isContractum';
                    redex := redex';
                    print_endline "];"))
                | _ -> ())
        | _ -> ());
        print_string (name^" [label=\""^label^"\" ");
        if x == thing then print_string " color=blue ";
        if isResult then print_string " fillcolor=\"#ccccff\" style=filled ";
        if !isContractum then print_string " shape=diamond  ";
        if !isConstructedInMain then print_string " fillcolor=\"#aaffaa\" style=filled ";
        print_endline "];";
        );
        (match !redex, parentRedex with
            | Some (r, c), _
            | _, Some (r, c) ->
                if not (isMain r) then
                    print_endline ((emit' x) ^ " -> " ^ (emit' r) ^ "[style=dotted label=\""^c^"\"];")
            | Some _, Some _ -> failwith "2redex!?"
            | _ -> ());
    
        (* if not !drewContractum then  *)
        (* Q-MULTIPLE-CONTRACTUMS? *)
        (match parentContractum with
            | Some c -> print_endline ((emit' x) ^ " -> " ^ (emit' c) ^ "[style=dotted penwidth=3];")
            | _ -> ());
        (* (match x with
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
                        print_endline ((emit' x)^" -> "^(emit' v)^" [style=dotted label=\""^n^"\"];")
                    | _, None -> ()
                ) !attrs attrimpls
            | _ -> ()); *)
        makeOrGet x
    in
    print_endline "digraph {\nnode [fontname = \"monospace\"];\n";
    ignore (emit true None None thing);
    print_endline "}";
    close_out oc;
    ignore (Sys.command "bash draw.sh")