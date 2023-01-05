let ssub s n m = String.sub s n (m-n);;
let suf s n = let l = String.length s in ssub s n l;;

let rec space1 s = if String.length s < 2 then s else if (ssub s 0 2) = "  " then space1 (suf s 1) else 
String.concat "" [ssub s 0 1; space1 (suf s 1)] ;;

(* only for types *)
let rec spaceremove s = if s = "" then s else if s.[0] = ' ' then spaceremove (suf s 1) else String.concat "" [ssub s 0 1; spaceremove (suf s 1)];;

let rec rectify s = if String.length s < 2 then s else if List.mem s.[0] ['(';')';'.';'>'] && not (s.[1]=' ') then 
String.concat "" [ssub s 0 1;" ";rectify (suf s 1)] else
if not (s.[0] = ' ') && List.mem s.[1] ['(';')';'.';'-'] then String.concat "" [ssub s 0 1;" "; rectify(suf s 1)]  else
 String.concat "" [ssub s 0 1;rectify (suf s 1)];;

let rec remove list elem = match list with
 a::b -> if a = elem then remove b elem else a::(remove b elem)
  |_ -> list;;

let rec prefix l n = match l with
  a::b -> if n > 0 then a:: (prefix b (n-1)) else []
| [] -> [];;

let rec suffix l n = if n = 0 then l else suffix (List.tl l) (n-1);;

let sub l n m = prefix (suffix l n) (m-n);;

let rec occ str car = if (String.length str > 0) then if str.[0] = car then true else occ (String.sub str 1 ((String.length str)-1 )) car else false;;

let rec split str car = if (occ str car) = false then [str] else
 let a = (String.index str car) in  [String.sub str 0 a ] @ split (String.sub str (a+1) ((String.length str)-a-1)) car;;

let lexer s = split (rectify (space1 s)) ' ';;

let rec double f list = match list with
(e, c::d) -> if ((f (List.rev e) ) && (f (c::d))) then true else double f (c::e, d)
| (e,[]) -> false;;

let seek f list = double f ([],list);;

let rec sdouble f list s = match list with
(e,c::d) -> if (f (List.rev e )) && c = s && f d then true else sdouble f (c::e, d) s
| (e, []) -> false;;

let ssseek f list s = sdouble f ([],list) s;;

let rec sddouble f list s = match list with
(e,c::d) -> if (f (List.rev e )) && c = s && f d then (List.rev e, d) else sddouble f (c::e, d) s
| (e, []) -> ([],[]);;

let saseek f list s = sddouble f ([],list) s;;

let rec ddouble f list = match list with
(e, c::d) -> if (( f (List.rev e) ) && (f (c::d))) then (List.rev e, c::d) else ddouble f (c::e, d)
| (e, []) -> ([],[]) ;;

let sseek f list = ddouble f ([], list);;

let rec sparse list = match list with
 [a] -> true
| a::b -> if List.nth list 0 = "(" && List.nth list (List.length list -1) = ")" && ssseek sparse (sub list 1 (List.length list - 1)) "->"  then true else false
| _ -> false ;;

let baselexer1 s = let aux = split  s ',' in List.map (function y -> split y ':' ) aux  ;;

let rec psrem a = match a with
x::y -> spaceremove x::psrem y
|_-> [];;

let fix l = List.map psrem l;;

let rec parse list = match list with
 [a] -> true
| a::b ->  if List.nth list 0 = "(" && List.nth list (List.length list -1) = ")" && seek parse (sub list 1 (List.length list - 1)) then true else
if List.length list > 3 && List.nth list 0  = "lambda" && not(List.mem (List.nth list 1) ["(";")";"."]) && List.nth list 2 = "." && parse (sub list 3 (List.length list)) then true else  false
| _ -> false;;

type lamtype = OTyVar of string | NTyVar of int | Arrow of lamtype * lamtype;;
type lamterm = TerVar of string | Abs of string* lamterm | App of lamterm*lamterm;;

let frame list = sub list 1 (List.length list -1);;

let rec ast list = if List.nth list 0 = "(" && List.nth list (List.length list -1) = ")"  then let n = sseek parse (frame list) in
 App (ast (fst n), ast (snd n)) else 
if List.nth list 0 = "lambda" then Abs (List.nth list 1, ast (sub list 3 (List.length list)))
else TerVar (List.nth list 0);;

let rec tyast list =  if List.nth list 0 = "(" && List.nth list (List.length list -1) = ")"  then let n = saseek sparse (frame list) "->" in
 Arrow (tyast (fst n), tyast (snd n)) else OTyVar (List.nth list 0);;


let past a = (ast (lexer(List.nth a 0)), tyast (lexer(List.nth a 1)));; 


let basegen s = if fix (baselexer1 s) = [[""]] then [] else List.map past ( fix (baselexer1 s));;let rec max l = match l with
 a::b -> if a > max b then a else max b
| [] -> 0;;

let varstack = ref 0;;
let inc() = varstack:= !varstack + 1;;
let reset() = varstack:= 0;;
let lmax l = max (List.map max l);;

let newone () = inc(); (NTyVar !varstack) ;;
let newtwo () = let a = newone () in let b = newone() in  (a,b);; 
let lambdavar t = match t with
 Abs (a,b) -> TerVar a
| _ -> failwith "not a lambda term";;
let last l = List.hd (List.rev l);;
type const = Eq of lamtype * lamtype | Bot | Ex of lamtype * const * const | BEx of lamtype * lamtype * const * const ;;
let last a = List.hd (List.rev a);;
let body a = List.tl (List.rev a);;
let newhead d h = List.rev (h::(List.tl (List.rev d)));; 
let rec transform dec = match last dec with
 (TerVar a,b) -> if (List.mem_assoc (TerVar a) (body dec)) then Eq (List.assoc (TerVar a) (body dec), b) else Bot 
|(Abs (v,t), b ) -> let (n,m) = (newtwo ()) in BEx (n,m, transform (newhead ((TerVar v,n)::dec) (t,m) ), Eq (b, Arrow (n,m)))
|(App (x,y) , b) -> let n = newone () in Ex (n,  transform (newhead dec (x, Arrow (n,b) ) ), transform (newhead dec (y, n)  ));;

let rec flatten co = match co with
 (Eq (a,b)) -> [(a,b)]
| (Ex (a,b,c)) -> (flatten b) @ (flatten c)
| (BEx (a,b,c,d)) -> (flatten c) @ (flatten d)
| Bot -> failwith "missing variable typing";;

let tes =  [   (  Abs ("x", Abs ("y", App (TerVar "x", App (TerVar "y", Abs ( "x", TerVar "y") )  )  )   ) ,  OTyVar "X" )   ];;

let tes2 = [ (TerVar "x", Arrow ( OTyVar "A", OTyVar "B") ); (Abs ("x", App (TerVar "x", TerVar "x")), OTyVar "X")];;

let rec sdecompose pair = match pair with
 ( Arrow (a,b)   , Arrow (c,d)   ) ->  (sdecompose (a,c)) @ (sdecompose (b,d))
| _ ->  [pair];;

let rec decompose l = match l with
 a::b -> (sdecompose a) @ (decompose b)
|[] -> [];;

let inference b s =  flatten (transform ((basegen b)@[( ast (lexer s), OTyVar "X")]) );;

let rec pairtolist l = match l with
(a,b):: y -> [a;b]:: pairtolist y
|_ -> [];;

let rec lpairtolist l = match l with
x::y -> pairtolist x :: lpairtolist y
|_-> [];;

let infer b s = pairtolist (inference b s);;

let checkarrow l = match l with
 Arrow (a,b ) -> true
|_ -> false;;

let rec lcheckarrow l = match l with
 x::y -> if checkarrow x then x else lcheckarrow y
|_ -> OTyVar "fail";;
 
let rec findeq l = match l with
 x::y -> if checkarrow x && not (lcheckarrow y = OTyVar "fail") then (pairtolist (sdecompose (x, lcheckarrow y) ) ) @ (findeq y) else findeq y
|_-> [];;

let rec purge l = match l with
 x::y -> if checkarrow x && not (lcheckarrow y = OTyVar "fail") then purge y  else x:: purge y
 |_-> [];;

let rec lpurge l = match l with
x::y -> if List.length (purge x) > 1 then purge x :: lpurge y else lpurge y
|_->[];;

let rec lfindeq l = match l with
 x::y -> (findeq x) @  lfindeq y 
 | _-> [];;

let reduce l = lfindeq l @ lpurge l;;

let preprocess b s = reduce (infer b s);;

let rec vremove set maze = if (List.length maze > 0) then match (List.hd maze) with
 (a,b) -> if ((List.mem a set) || (List.mem b set)) then vremove set (List.tl maze) else (a,b)::(vremove set (List.tl maze))
else [];;

let rec next comp maze = if (List.length maze > 0 ) then  match (List.hd maze) with
 (a,b) -> if ((List.mem a comp) && not (List.mem b comp) ) then  List.rev (b::(List.rev comp))
 else if ((List.mem b comp) && not (List.mem a comp) ) then List.rev (a::(List.rev comp)) else next comp (List.tl maze) else comp;;

let rec connect start maze = if (next start maze = start) then start else connect (next start maze) maze;;

let rec check comp maze = if (List.length maze > 0) then match (List.hd maze) with
 (a,b) -> if (not (List.mem a comp) && not (List.mem b comp)) then [a] else check comp (List.tl maze) else [] ;;

let rec concomp start maze = if start = [] then [] else let a = connect start maze in let b = check a maze in a :: (concomp b (vremove a maze)) ;;

let rec intersection a b = match a with
 x::y -> if List.mem x b then true else intersection y b
 | _ -> false;;

let rec merge a list = match list with
 x::y -> if (intersection a x = true) && not (a = x)  then (a @ x) :: (remove list x) else x::(merge a y)
| _ -> list

let rec merge2 list = match list with
x::y -> if merge x list = list then x::merge2 y else remove (merge x list) x
| _ -> list;;
 
let rec merge3 list = if (merge2 list = list) then list else merge3 (merge2 list);;

let rec double a list = match list with
 x::y -> if a = x && List.mem x y  then double a y else x:: double a y
|_-> list;;

let rec double2 list = match list with
x::y -> if double x list = list then x::(double2 y) else double2 (double x list)
|_-> list;;

let rec double3 list = match list with
x::y -> double2 x :: double3 y
|_-> [];;

let process l = double3 (merge3 (reduce l));;

let rec uprocess l = if process l = l then l else uprocess (process l);;

let rec order l = match l with
 x::y -> if checkarrow x then List.rev l else x::order y
|_-> l;;

let rec lorder l = List.map order l;;

let rec display1 x = match x with
 Arrow (a,b) -> String.concat "" ["( "; display1 a; " -> "; display1 b; " )" ]
 |OTyVar a -> a
 |NTyVar n -> String.concat "" ["X_"; string_of_int n]

let display2 l = List.map display1 l;;

let display3 l = String.concat " => " (display2 l);;

let display4 l = List.map display3 l;;

let rec display5 l = match l with
 x::y -> print_string (String.concat "" [x;"\n"]); display5 y
 |_-> ();;

let display l = display5 (display4 l);;

let typeinfer b s =  display   (lorder (uprocess  (preprocess b s)));;
(*print_string "\nEnter Closed Term: \n";let input = read_line () in typeinfer input;;*)

let ti b s = lorder (uprocess (preprocess b s));;

let a = "(lambda x. x lambda x. lambda y . (x (x y)))";;
