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
type 'a lz = 'a Lazy.t
let force = Lazy.force