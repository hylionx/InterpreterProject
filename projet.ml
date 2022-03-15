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
let rec prop_to_string prop =
  match prop with 
   Prop(cst) -> bexp_to_string cst
|  And(c1, c2) -> "(" ^ prop_to_string c1 ^ ")&&(" ^ prop_to_string c2 ^")"
| Implied(c1,c2) -> "(" ^ prop_to_string c1 ^ ")=>(" ^ prop_to_string c2 ^")"
| Or(c1,c2) -> "(" ^ prop_to_string c1 ^ ")\/(" ^ prop_to_string c2 ^")"
| Not(cst) -> "¬" ^  prop_to_string cst
| Equal(v1, v2) -> aexp_to_string v1 ^"="^ aexp_to_string v2
| NotEqual(v1, v2) -> aexp_to_string v1 ^"!="^ aexp_to_string v2
| Inf(v1, v2) -> aexp_to_string v1 ^"<"^ aexp_to_string v2
| InfEqual(v1, v2) -> aexp_to_string v1 ^"<="^ aexp_to_string v2
;;

prop_to_string tpropTrue;;
prop_to_string tpropFalse;;

prop_to_string tprop2_1;;
prop_to_string tprop2_2;;
prop_to_string tprop2_3;;
prop_to_string tprop2_4;;

prop_to_string tprop3_1;;
prop_to_string tprop3_2;;
prop_to_string tprop3_3;;

prop_to_string tprop4_1;;
prop_to_string tprop4_2;;

prop_to_string tprop5;;

(* Question 4 : *)
let rec pinterp formula valuation =
  match formula with 
   Prop(cst) -> binterp cst valuation
|  And(p, q) -> (pinterp p valuation) && (pinterp q valuation)
| Implied(p,q) -> not(pinterp p valuation) || (pinterp q valuation)
| Or(p,q) -> (pinterp p valuation) || (pinterp q valuation)
| Not(p) -> not(pinterp p valuation)
| Equal(v1, v2) ->(ainterp v1 valuation) = (ainterp v2 valuation)
| NotEqual(v1, v2) ->(ainterp v1 valuation) != (ainterp v2 valuation)
| Inf(v1, v2) -> (ainterp v1 valuation) < (ainterp v2 valuation)
| InfEqual(v1, v2) -> (ainterp v1 valuation) <= (ainterp v2 valuation)
;;

(* Question 5: *)
let valuation1_4 = [("x", 7);("y", 3) ];;

pinterp tpropTrue valuation1_4 ;;
pinterp tpropFalse valuation1_4;;

pinterp tprop2_1 valuation1_4;;
pinterp tprop2_2 valuation1_4;;
pinterp tprop2_3 valuation1_4;;
pinterp tprop2_4 valuation1_4;;

pinterp tprop3_1 valuation1_4;;
pinterp tprop3_2 valuation1_4;;
pinterp tprop3_3 valuation1_4;;

pinterp tprop4_1 valuation1_4;;
pinterp tprop4_2 valuation1_4;;

pinterp tprop5 valuation1_4;;
