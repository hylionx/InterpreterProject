#use "prog.ml";;

(* 1.4  Triplets de Hoare et validit� *)

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
| Not(cst) -> "�" ^  prop_to_string cst
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

(* Question 6: *)
let rec asubst var exp axp =
  match axp with
  | Add (aexpr1, aexpr2) -> Add((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Mult (aexpr1, aexpr2) -> Mult((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Minus (aexpr1, aexpr2) -> Minus((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Var v -> if (v = var) then exp else Var v
  | Const v -> axp
;;

let rec bsubst var exp bxp =
  match bxp with                     
  | Const _  ->  bxp
  | Or (bxp1,bxp2) -> Or((bsubst var exp bxp1), (bsubst var exp bxp2))
  | And (bxp1,bxp2) -> And((bsubst var exp bxp1), (bsubst var exp bxp2))
  | Not bxp1 -> Not(bsubst var exp bxp1)
  | Equal (bxp1,bxp2) -> Equal((asubst var exp bxp1), (asubst var exp bxp2))
  | InfEqual (bxp1,bxp2) ->InfEqual((asubst var exp bxp1), (asubst var exp bxp2))
;;


let rec psubst var exp formula =
  match formula with
   Prop(cst) -> Prop (bsubst var exp cst)
  |  And(p, q) -> And((psubst var exp p), (psubst var exp q))
  | Implied(p,q) -> Implied((psubst var exp p), (psubst var exp q))
  | Or(p,q) ->  Or((psubst var exp p), (psubst var exp q))
  | Not(p) -> Not(psubst var exp p)
  | Equal(v1, v2) ->Equal((asubst var exp v1), (asubst var exp v2))
  | NotEqual(v1, v2) ->NotEqual((asubst var exp v1), (asubst var exp v2))
  | Inf(v1, v2) -> Inf((asubst var exp v1), (asubst var exp v2))
  | InfEqual(v1, v2) -> InfEqual((asubst var exp v1), (asubst var exp v2))
;;

(* Question 7: *)
let rec applied var new_exp list =
  match list with
    [] -> []
  | head::tail -> (psubst var new_exp head)::(applied var new_exp tail) 
;;
let rec printListProp list =
  match list with
    [] -> ""
  | head::tail -> (prop_to_string head) ^"\n"^ printListProp tail
;;


let list_prop = [tpropTrue;tpropFalse;tprop2_1;tprop2_2;tprop2_3;tprop2_4;tprop3_1;tprop3_2;tprop3_3;tprop4_1;tprop4_2];;

let expx = Mult(Const 3, Var "y");;
let expy = Add(Var "k", Const 2);;

(*print_string(printListProp list_prop);;*)
let list_prop = applied "y" expy list_prop;;
let list_prop = applied "x" expx list_prop;; 
(*print_string(printListProp list_prop);;*)