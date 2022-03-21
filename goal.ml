#load "str.cma";;

#use "bxpr.ml";;
#use "projet.ml";;
#use "hoare_triple.ml";;

type goal =
  ContextHoare of (string*tprop)list * hoare_triple
  |ContextTprop of (string*tprop)list *  tprop
;;



let p : tprop = Prop(Const true);;
let q : tprop = Prop(Const false);;
let r : tprop = Prop(Const true);;
let impl : tprop = Implied ((Or (p, q)), r);;

let context1 = [("H", impl) ; ("H2", p)];;
let conclusion1 = Or (p, q);;

(* Question 2 : *)
let goal1 = ContextTprop ( context1, conclusion1 );;
(*context : [H : (P \/ Q => R); H2 : P] conclusion : P \/ Q*)

 
let goal2: hoare_triple = Hoare (Equal (Var "x", Const (-3)),
                                  Cond(
                                      InfEqual(Var "x", Const 0),
                                      Affect("x", Minus(Const 0, Var "x")),
                                      Skip),
                                  Equal(Const 3, Var "x")              
                             )
;;

(* {True} if x <= 0 then r := 0-x else r := x {0 <= r } *)
