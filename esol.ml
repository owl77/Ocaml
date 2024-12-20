

let rec pre_bin_op_bool sep parser_bool pairexp = match pairexp with
  (a,b::c) -> if parser_bool (List.rev a) && parser_bool c && b = sep then true else pre_bin_op_bool sep parser_bool (b::a ,  c)
  | (a,[]) -> false;; 

let rec pre_bin_op sep parser_bool pairexp = match pairexp with
  (a,b::c) -> if parser_bool (List.rev a) && parser_bool c && b = sep then (List.rev a , c) else pre_bin_op sep parser_bool (b::a ,  c)
  | (a,[]) -> (a,[]);;

let rec pre_bin_op_star_bool sep parser_bool pairexp = match pairexp with
 (a, b::c)  -> if parser_bool (List.rev a) && pre_bin_op_star_bool sep parser_bool ([],c) && b = sep then true else pre_bin_op_star_bool sep parser_bool (b::a, c)
 |(a, []) -> false;;

let rec pre_bin_op_star sep parser_bool pairexp = match pairexp with
  (a,b::c) ->  if parser_bool (List.rev a) && pre_bin_op_star_bool sep parser_bool ([],c) && b = sep then (List.rev a)::(pre_bin_op_star sep parser_bool ([],c) ) else
pre_bin_op_star sep parser_bool (b::a,c)
 | (a,[]) -> [];;

let rec pre_star_bool  parser_bool pairexp = match pairexp with
 (a, b::c)  -> if parser_bool (List.rev a) && pre_star_bool  parser_bool ([],b::c) then true else pre_star_bool parser_bool (b::a, c)
 |(a, []) -> false;;

let rec pre_star  parser_bool pairexp = match pairexp with
  (a,b::c) ->  if parser_bool (List.rev a) && pre_star_bool parser_bool ([],b::c)  then (List.rev a)::(pre_star  parser_bool ([],b::c) ) else
pre_star parser_bool (b::a,c)
 | (a,[]) -> [];;

let rec pre_2bin_op_bool sep parser1_bool parser2_bool pairexp = match pairexp with
  (a,b::c) -> if parser1_bool (List.rev a) && parser2_bool c && b = sep then true else pre_2bin_op_bool sep parser1_bool parser2_bool (b::a ,  c)
  | (a,[]) -> false;; 

let rec pre_2bin_op sep parser1_bool parser2_bool pairexp = match pairexp with
  (a,b::c) -> if parser1_bool (List.rev a) && parser2_bool c && b = sep then (List.rev a , c) else pre_2bin_op sep parser1_bool parser2_bool (b::a ,  c)
  | (a,[]) -> (a,[]);;

let rec pre_2bin_bool parser1_bool parser2_bool pairexp = match pairexp with
  (a,b::c) -> if parser1_bool (List.rev a) && parser2_bool (b::c) then true else pre_2bin_bool parser1_bool parser2_bool (b::a ,  c)
  | (a,[]) -> false;; 

let rec pre_2bin  parser1_bool parser2_bool pairexp = match pairexp with
  (a,b::c) -> if parser1_bool (List.rev a) && parser2_bool (b::c)  then (List.rev a , c) else pre_2bin parser1_bool parser2_bool (b::a ,  c)
  | (a,[]) -> (a,[]);;


type info = Info of int*bool;;

type argumentSig = PredicateSig of int | IndividualSig;;
type formula = Bot | App of term*(term list) | 
And of formula*formula | Or of formula*formula | 
Neg of formula | Imp of formula*formula | 
Forall of term*formula | Exists of term*formula
and term = Constant of string*argumentSig | 
Variable of string*argumentSig*info | Lambda of (term list)* formula;;

let rec indVarCheck list = match list with
 []    -> true
 | a:: b ->  match a with
             Variable (x , y , i ) -> if y = IndividualSig then (indVarCheck b) else false
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
                |Variable (s,arg,i) -> (List.length l) = (arity arg)) && (mapBool appCheckT l)
 |_ -> true;;



let rec quantCheckT term = match term with
  Lambda (x, g) -> quantCheckF g 
  |_ -> true
 and  quantCheckF form = match form with 
  Forall (x,f) ->  (match x with
                         Variable (a,b,i) -> quantCheckF f
                         |_ -> true)
 | Exists (x,f) ->  (match x with
                         Variable (a,b,i) -> quantCheckF f
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
  Variable(s,arg,i) -> (match w with 
                           Variable(t,arg2,j) ->  s = t 
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
| Variable (s,arg,i) -> if not (var_mem (Variable (s,arg,i)) bag) then [Variable (s,arg,i)] else []
|_ ->  [] ;;
