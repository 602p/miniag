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
    | x -> "["^([%show:value] x)^"]"

let getComment = function (_, _, _, c) -> c

let rec string_of_oi = function
    | None, _ -> "None"
    | Some (x, r), s -> "Some -- "^s^"\n -- linked rule: "^
        (match r with
            | None -> "None"
            | Some r -> "#"^(getComment r))
        ^"\n -- linked value: "^(actually_pretty_print x)^(match x with
        | BareNonterminalV(_, _, oi)
        | DecoratedNonterminalV(_, _, _, oi) ->
            "\n\n -> "^(string_of_oi oi)
        | _ -> "\n\n -> X")

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


