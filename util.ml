let swap2 f y x = f x y
let thog f g x = f (g x)
let negatep f x = not (f x)
let rec stringJoin j = function
    | [] -> ""
    | [x] -> x
    | x::xs -> x ^ j ^ (stringJoin j xs)
let rec zip l1 l2 = match (l1, l2) with
    | x::xs, y::ys -> (x, y)::zip xs ys
    | [], [] -> []
    | _ -> failwith "zip of non-equal-length lists"
let enforce (cond : bool) (msg : string) : unit = if not cond then failwith ("enforcefail: "^msg) else ()
let warnifnot (cond : bool) (msg : string) : unit = if not cond then print_endline msg else ()
type 'a lz = 'a Lazy.t [@@ deriving show]
let force = Lazy.force
let assoc (x : string) (y : (string * 'a) list) : 'a = match List.assoc_opt x y with
    | None -> failwith ("assoc failure: "^x)
    | Some z -> z
let assertSome = function
    | Some x -> x
    | None -> failwith "assertSome"

let findNth lst x = let rec findNth' x lst c = match lst with
        | [] -> failwith "Not Found"
        | hd::tl -> if (hd=x) then c else findNth' x tl (c+1) in
    findNth' x lst 0

let findNthI lst x = let rec findNth' x lst c = match lst with
        | [] -> failwith "Not Found"
        | hd::tl -> if (hd==x) then c else findNth' x tl (c+1) in
    findNth' x lst 0

let findNthP lst x = let rec findNthP' x lst c = match lst with
        | [] -> failwith "Not Found"
        | hd::tl -> if (x hd) then c else findNthP' x tl (c+1) in
    findNthP' x lst 0

let flatMap f x = List.flatten (List.map f x)

let rec applyFirst f z xs = match xs with
    | [] -> z
    | x::xs -> match f x with
        | Some r -> r
        | None -> applyFirst f z xs

let rec applyFirstOpt (f : 'a -> 'b option) (l : 'a list) : 'b option = match l with
    | [] -> None
    | x::xs -> match f x with
        | Some r -> Some r
        | None -> applyFirstOpt f xs

let rec filterMap f = function
    | [] -> []
    | x::xs -> match f x with
        | Some r -> r::filterMap f xs
        | None -> filterMap f xs

let splitPairList l = (List.map fst l, List.map snd l)
let fst2 (a, b, _) = (a, b)
let snd2 (_, b, c) = (b, c)

let listAll p l = List.fold_left (&&) true (List.map p l)
let listAny p l = List.fold_left (||) false (List.map p l)


let containsRe s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false
