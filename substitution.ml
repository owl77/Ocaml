#use "maze.ml";;

let rec prod body tail = match body with
 x::y -> (x, tail):: prod y tail
 |_-> [];;

let sub data = prod (tailess data) (last data);;

let rec lsub list = match list with
 x::y -> (sub x)@lsub y
|_-> [];;

let rec replace f r = match f with
 Arrow (a,b) -> Arrow (replace a r, replace b r)
| OTyVar x -> if List.mem_assoc (OTyVar x) r then List.assoc (OTyVar x) r else OTyVar x
| NTyVar x -> if List.mem_assoc (NTyVar x) r then List.assoc (NTyVar x) r else NTyVar x;;

let rec findtype1 f r = if replace f r = f then f else findtype1 (replace f r) r;;

let findtype data = findtype1 (OTyVar "X") (lsub data);;

let alph = [OTyVar "'a";OTyVar "'b"; OTyVar"'c";OTyVar"'d";OTyVar"'e";OTyVar"'f";OTyVar"'g"]

let used = ref [];;

let rec nice f = match f with
 Arrow (a,b) -> nice a; nice b
| NTyVar x -> if not (List.mem (NTyVar x) !used ) then used := (NTyVar x)::!used else ()
| OTyVar x -> ();;
 
let pretty f = let w =  List.combine !used (prefix alph (List.length !used) ) in replace f w;;


 (*to check if a lambda-term is typable cycle (ti [BASE] [TERM]) *)
(* to show type display1 pretty findtype (ti [BASE] [TERM]) *)

let typable a b = not (cycle (ti a b));;
let showtype a b = let x = findtype (ti a b) in (nice x);display1 (pretty x);;

let typer a b = let y = ti a b in if not (cycle y) then let x = findtype y in (nice x);display1 (pretty x) else "Not typable.";;


