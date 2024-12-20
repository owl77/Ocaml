
let opt_to_bool op = match op with
 Some x -> true
|None -> false;;

let opt_to_list op = match op with
 Some x -> x
| None -> [];;

let rec lookup k = function
| [] -> None
| (k', v) :: t -> if k = k' then Some v else lookup k t

let insert k v lst = (k, v) :: lst


let rec bin_op sep parser1 parser2 pairexp = match pairexp with
  (a,b::c) -> if opt_to_bool (parser1 (List.rev a)) && opt_to_bool(parser2 c) && b = sep then Some (List.rev a, c) else bin_op sep parser1 parser2 (b::a ,  c)
  | (a,[]) -> None;;


let rec sep_star sep parser pairexp = match pairexp with
  (a,b::c) ->  if opt_to_bool( parser (List.rev a)) && opt_to_bool(sep_star sep parser ([],c)) && b = sep then Some ((List.rev a)::opt_to_list (sep_star sep parser ([],c) ))
   else sep_star sep parser (b::a,c)
 | (a,[]) -> None;;

let rec star parser pairexp = match pairexp with
  (a,b::c) ->  if opt_to_bool( parser (List.rev a)) && opt_to_bool(star parser ([],b::c))  then Some ((List.rev a)::opt_to_list (star parser ([],b::c) ))
   else star parser (b::a,c)
 | (a,[]) -> None;;

let simple_parse list exp = if List.length exp = 1 && List.mem (List.nth exp 0) list then Some true else None;;

let variable_parser dic exp = if List.length exp = 1 && opt_to_bool(lookup (List.nth exp 0) dic) then (match  lookup (List.nth exp 0) dic with
 Some (x,y) -> Some (Variable (List.nth exp 0 , (x , y))  )
| None -> None )  else None;;

let constant_parser dic exp = if List.length exp = 1 && opt_to_bool(lookup (List.nth exp 0) dic) then (match  lookup (List.nth exp 0) dic with
 Some x -> Some (Constant (List.nth exp 0 , x )  )
| None -> None )  else None;;


let rec or_parser parser_list exp = match parser_list with
 a::b -> if  opt_to_bool (a exp) then (a exp) else or_parser b exp
|_ -> None;;





type info = Info of int*bool;;

type argumentSig = PredicateSig of int | IndividualSig;;
type formula = Bot | App of term*(term list) | 
And of formula*formula | Or of formula*formula | 
Neg of formula | Imp of formula*formula | 
Forall of term*formula | Exists of term*formula
and term = Constant of string*argumentSig | 
Variable of string*(argumentSig*info) | Lambda of (term list)* formula;;

let rec indVarCheck list = match list with
 []    -> true
 | a:: b ->  match a with
             Variable (x , (y , i) ) -> if y = IndividualSig then (indVarCheck b) else false
             |_ -> false;;

let arity arg = match arg with
  PredicateSig n -> n 
  |_ -> -1;;               

let rec mapBool cond list = match list with
 [] -> true
| a:: b -> if (cond a) then (mapBool cond b) else false;;

 
let rec appCheckT term = match term with
  Lambda (x, g) -> appCheckF g 
  |_ -> true
 and  appCheckF form = match form with 
  Forall (x,f) ->  appCheckF f
 | Exists (x,f) -> appCheckF f
 | And (f,g)  ->  (appCheckF f) && (appCheckF g)
 | Or (f,g)    ->   (appCheckF f) && (appCheckF g)
 | Imp (f,g)   ->  (appCheckF f) && (appCheckF g)
 | Neg f     -> appCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  -> ((List.length x) = (List.length l)) && (indVarCheck x) && appCheckF g && (mapBool appCheckT l)
                |Constant (s,arg) -> (List.length l) = (arity arg) && (mapBool appCheckT l)  
                |Variable (s,(arg,i)) -> (List.length l) = (arity arg)) && (mapBool appCheckT l)
 |_ -> true;;



let rec quantCheckT term = match term with
  Lambda (x, g) -> quantCheckF g 
  |_ -> true
 and  quantCheckF form = match form with 
  Forall (x,f) ->  (match x with
                         Variable (a,(b,i)) -> quantCheckF f
                         |_ -> true)
 | Exists (x,f) ->  (match x with
                         Variable (a,(b,i)) -> quantCheckF f
                         |_ -> true)
 | And (f,g)  ->  (quantCheckF f) && (quantCheckF g)
 | Or (f,g)    ->   (quantCheckF f) && (quantCheckF g)
 | Imp (f,g)   ->  (quantCheckF f) && (quantCheckF g)
 | Neg f     -> quantCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  ->  quantCheckF g && (mapBool quantCheckT l)
                |_ -> mapBool quantCheckT l )
 |_ -> true;;

let checkF exp = (appCheckF exp) && (quantCheckF exp);;

let var_eq v w = match v with
  Variable(s,(arg,i)) -> (match w with 
                           Variable(t,(arg2,j)) ->  s = t 
                           |_ -> false)
  |_ -> false;;

let rec var_mem v list = match list with
  a::b  -> if (var_eq a v) then true else var_mem v list
  |_ -> false;;


let rec freeVariablesF bag form = match form with
  And (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Or (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Imp (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Neg f -> freeVariablesF bag f
| Bot ->  []
| Forall (x,f)  ->   freeVariablesF (bag @ [x]) f 
| Exists (x,f)  ->   freeVariablesF (bag @ [x]) f
| App (t,l)  ->  (freeVariablesT bag t) @  (List.concat (List.map (fun x -> freeVariablesT bag x)  l))
and
freeVariablesT bag term = match term with
 Lambda (x,g) ->  freeVariablesF (bag @ x) g
| Variable (s,(arg,i)) -> if not (var_mem (Variable (s,(arg,i))) bag) then [Variable (s,(arg,i))] else []
|_ ->  [] ;;
