
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

 let appCheckT form = match form with
  App (t,l) -> (match t with
                Lambda (x, g) -> ((List.length x) = (List.length l)) && (indVarCheck x)
                |Constant (s,arg) -> (List.length l) = (arity arg) 
                |Variable (s,arg) -> (List.length l) = (arity arg))
  |_ -> true;;              
 

let rec quantCheck form = match form with 
  Forall (x,y,f) ->   (match x with
                      Variable (a,b) -> quantCheck f
                      |_ -> false)
 | Exists (x,y,f) ->  (match x with
                         Variable (a,b) -> quantCheck f
                       |_ -> false)

 | And (f,g)  ->  (quantCheck f) && (quantCheck g)
 | Or (f,g)    ->   (quantCheck f) && (quantCheck g)
 | Imp (f,g)   ->  (quantCheck f) && (quantCheck g)
 | Neg f     -> quantCheck f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  ->  quantCheck g 
                 |_ -> true )
 |_ -> true;;

let rec appCheck form = match form with 
  Forall (x,y,f) ->  appCheck f
 | Exists (x,y,f) -> appCheck f
 | And (f,g)  ->  (appCheck f) && (appCheck g)
 | Or (f,g)    ->   (appCheck f) && (appCheck g)
 | Imp (f,g)   ->  (appCheck f) && (appCheck g)
 | Neg f     -> appCheck f
 | App (t,l) -> appCheckT (App (t,l)) &&  (match t with 
                  Lambda (x,g)  ->  appCheck g 
                 |_ -> true )
 |_ -> true;;


