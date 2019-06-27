let swap2 f y x = f x y
let thog f g x = f (g x)
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

let findNthP lst x = let rec findNthP' x lst c = match lst with
	    | [] -> failwith "Not Found"
	    | hd::tl -> if (x hd) then c else findNthP' x tl (c+1) in
    findNthP' x lst 0

let flatMap f x = List.flatten (List.map f x)