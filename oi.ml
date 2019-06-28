open Corelang

let rec string_of_oi = function
    | None, _ -> "None"
    | Some (x, r), s -> "Some -- cause: \""^s^"\"\n -- linked rule: "^
        (match r with
            | None -> "(None)"
            | Some r -> "(Some "^([%show:attrrule] r)^")")
        ^"\n - linked value: "^([%show: value] x)^(match x with
        | BareNonterminalV(_, _, oi)
        | DecoratedNonterminalV(_, _, _, oi) ->
            "\n -> "^(string_of_oi oi)
        | _ -> "\n -> X")