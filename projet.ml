#use "prog.ml";;

(* 1.4  Triplets de Hoare et validité *)

(* Question 1 : *)
type tprop =
 Prop of bexpr
|  And of tprop * tprop
| Implied of tprop * tprop
| Or of tprop * tprop
| Not of tprop
| Equal of aexpr * aexpr
| NotEqual of aexpr * aexpr
| Inf of aexpr * aexpr
| InfEqual of aexpr * aexpr
;;


(* Question 2 : *)
let tpropTrue = Prop (Const true);;
let tpropFalse = Prop (Const false);;

let tprop2_1 = And(tpropTrue, tpropFalse);;
let tprop2_2 = Not(tpropTrue);;
let tprop2_3 = Or(tpropTrue, tpropFalse);;
let tprop2_4 = Implied(tpropFalse,tprop2_3);;

let tprop3_1 = Equal(Const 2, Const 4);;
let tprop3_2 = Equal(Add(Const 3, Const 5), Mult(Const 2, Const 4));;
let tprop3_3 = Equal(Mult(Const 3, Var "x"), Add(Var "y", Const 1));;

let tprop4_1 = InfEqual(Add(Const 3, Var "x"), Mult(Const 4, Var "y"));;
let tprop4_2 = And(
                   InfEqual(Const 5, Const 7),
                   InfEqual(Add(Const 8, Const 9), Mult(Const 4, Const 5))
                 );;

let tprop5 = Implied(Equal(Var "x", Const 1), InfEqual(Var "y", Const 0));;


(* Question 3 : *)
let prop_to_string prop =
   Prop(
|  And of tprop * tprop
| Implied of tprop * tprop
| Or of tprop * tprop
| Not of tprop
| Equal of aexpr * aexpr
| NotEqual of aexpr * aexpr
| Inf of aexpr * aexpr
| InfEqual of aexpr * aexpr
;;
