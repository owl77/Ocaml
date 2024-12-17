
type argumentSig = PredicateSig of int | IndividualSig;;
type formula = Bot | App of term*(term list) | 
And of formula*formula | Or of formula*formula | 
Neg of formula | Imp of formula*formula | 
Forall of term* argumentSig*formula | Exists of term* argumentSig*formula
and term = Constant of string*argumentSig | 
Variable of string*argumentSig | Lambda of (term list)* formula;;

let rec indVarCheck list = match list with
 []    -> true
 | a:: b ->  match a with
             Variable (x , y) -> if y = IndividualSig then (indVarCheck b) else false
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
  Forall (x,y,f) ->  appCheckF f
 | Exists (x,y,f) -> appCheckF f
 | And (f,g)  ->  (appCheckF f) && (appCheckF g)
 | Or (f,g)    ->   (appCheckF f) && (appCheckF g)
 | Imp (f,g)   ->  (appCheckF f) && (appCheckF g)
 | Neg f     -> appCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  -> ((List.length x) = (List.length l)) && (indVarCheck x) && appCheckF g && (mapBool appCheckT l)
                |Constant (s,arg) -> (List.length l) = (arity arg) && (mapBool appCheckT l)  
                |Variable (s,arg) -> (List.length l) = (arity arg)) && (mapBool appCheckT l)
 |_ -> true;;



let rec quantCheckT term = match term with
  Lambda (x, g) -> quantCheckF g 
  |_ -> true
 and  quantCheckF form = match form with 
  Forall (x,y,f) ->  (match x with
                         Variable (a,b) -> quantCheckF f
                         |_ -> true)
 | Exists (x,y,f) ->  (match x with
                         Variable (a,b) -> quantCheckF f
                         |_ -> true)
 | And (f,g)  ->  (quantCheckF f) && (quantCheckF g)
 | Or (f,g)    ->   (quantCheckF f) && (quantCheckF g)
 | Imp (f,g)   ->  (quantCheckF f) && (quantCheckF g)
 | Neg f     -> quantCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  ->  quantCheckF g && (mapBool quantCheckT l)
                |_ -> mapBool quantCheckT l )
 |_ -> true;;


