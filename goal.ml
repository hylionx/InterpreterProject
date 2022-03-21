#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;
#use "hoare_triple.ml";;

type goal =
  ContextHoare of (string*tprop)list * hoare_triple
  |ContextTprop of (string*tprop)list *  tprop
;;





type tprop =
 Prop of bexpr
| And of tprop * tprop
| Implied of tprop * tprop
| Or of tprop * tprop
| Not of tprop
| Equal of aexpr * aexpr
| NotEqual of aexpr * aexpr
| Inf of aexpr * aexpr
| InfEqual of aexpr * aexpr

;;

let p : tprop = Prop(Const true);;
let q : tprop = Prop(Const false);;
let r : tprop = Prop(Const true);;

(* Question 2 : *)
let goal1 : goal = ContextTprop (
                       [ ("H", Implied( Or p q), r)); ("H2", p) ],
                       (Or (p, q))
                     );;
(*• context : [H : (P ∨ Q ⇒ R); H2 : P] conclusion : P ∨ Q*)
 
