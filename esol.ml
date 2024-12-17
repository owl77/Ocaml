
type argumentSig = PredicateSig of int | IndividualSig;;
type formula = App of term*(term list) | 
And of formula*formula | Or of formula*formula | 
Neg of formula | Imp of formula*formula | 
Forall of string* argumentSig | Exists of string* argumentSig 
and term = Constant of string*argumentSig | 
Variable of string*argumentSig | Lambda of (term list)* formula;;
