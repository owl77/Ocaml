
#use "typeinference20jul.ml";;

let arrowcheck a = match a with
Arrow (_,_) -> true
|_ -> false;;

let rec extract t = match t with
NTyVar a -> [NTyVar a]
| OTyVar a -> [OTyVar a]
| Arrow(a,b) -> (extract a) @ (extract b);;


let rec findlist list = function 
a -> match list with
 x::y -> if List.mem a x then x else findlist y a
 |_ -> [a];;

let tailess l = if arrowcheck (last l) then List.rev (List.tl (List.rev l)) else l;;

let ltailess l = List.map tailess l;;

let lfindlist a list = List.map (findlist list) a;;

let maze1 data  = function
a ->  let x = last a in let y = ltailess data in if arrowcheck x then (tailess a, lfindlist (extract x) y) else (a,[]);;

let maze data = List.map (maze1 data) data;;


(*let mazing s a = let x = ltailess  (List.map  display2 (ti s)) in let y = extract (lexer (display1 a)) in  lfindlist y x;;*)

(*let maz s n = mazing s (last (List.nth (ti s) n));;*)

let rec findinit a = match ltailess a with
x::y -> if List.mem (OTyVar "X") x then x else findinit y
|_ -> [];;


let rec remove list elem = match list with
 a::b -> if a = elem then remove b elem else a::(remove b elem)
  |_ -> list;;

let rec assremove maze key value = match maze with
a::b -> if fst a = key then (key, remove (snd a) value)::b else a::assremove b key value 
|_-> [];;


let rec find used pos maze = if List.mem_assoc pos maze = false then false else
match List.assoc pos maze with
 x::y -> if List.mem x used then true else if (find (pos::used) x maze = false) then find used pos (assremove maze pos x) else true
|_-> false;;

let cycle a = reset();find [] (findinit a) (maze a);;

let lab = [("a",["b"] );("b",["c"] ); ("c",["d"] ); ("d",["b"] )];;

