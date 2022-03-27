#use "prog.ml";;

(* 1.4  Triplets de Hoare et validité *)

(* Question 1 : *)
(* type tprop donnant la syntaxte abstraite des formules logiques 
        - Prop qui represente les deux constantes vrai et faux 
        - And / Or / Implied qui correspondent aux connecteurs logiques 
        - Not pour la negation dune proposition 
        - Equal pour l egalite de deux expressions arithmetiques 
        - NotEqual pour l inegalite de deux expressions arithmetiques 
        - Inf l inferiorite entre deux expressions arithmetiques 
        - InfEqual inegalite inferieure ou egale pour deux expressions arithmetiques 
*)
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


(* Question 2 : *)
(* defintion de plusieurs propositions logiques  *)

(* vrai *)
let tpropTrue = Prop (Const true);;
(* faux *)
let tpropFalse = Prop (Const false);;

(* vrai et faux  *)
let tprop2_1 = And(tpropTrue, tpropFalse);;
(* non vrai  *)
let tprop2_2 = Not(tpropTrue);;
(* vrai ou faux  *)
let tprop2_3 = Or(tpropTrue, tpropFalse);;
(* faux implique vrai ou faux *)
let tprop2_4 = Implied(tpropFalse,tprop2_3);;

(* 2 = 4 *)
let tprop3_1 = Equal(Const 2, Const 4);;
(* 3+5 = 2*4 *)
let tprop3_2 = Equal(Add(Const 3, Const 5), Mult(Const 2, Const 4));;
(* 2*x = y+1 *)
let tprop3_3 = Equal(Mult(Const 3, Var "x"), Add(Var "y", Const 1));;

(*3+x <=4*y *)
let tprop4_1 = InfEqual(Add(Const 3, Var "x"), Mult(Const 4, Var "y"));;
(* (5<7) et (8+9 <= 4*5 *)
let tprop4_2 = And(
                   InfEqual(Const 5, Const 7),
                   InfEqual(Add(Const 8, Const 9), Mult(Const 4, Const 5))
                 );;
(* (x=1) implique (y<=0) *)
let tprop5 = Implied(Equal(Var "x", Const 1), InfEqual(Var "y", Const 0));;


(* Question 3 : *)
(* convertie une formule logique en une chaine de caractere  *)
let rec prop_to_string prop =
  match prop with 
   Prop(cst) -> bexp_to_string cst
|  And(c1, c2) -> "(" ^ prop_to_string c1 ^ ")/\(" ^ prop_to_string c2 ^")"
| Implied(c1,c2) -> "(" ^ prop_to_string c1 ^ ")=>(" ^ prop_to_string c2 ^")"
| Or(c1,c2) -> "(" ^ prop_to_string c1 ^ ")\/(" ^ prop_to_string c2 ^")"
| Not(cst) -> "¬" ^  prop_to_string cst
| Equal(v1, v2) -> aexp_to_string v1 ^"="^ aexp_to_string v2
| NotEqual(v1, v2) -> aexp_to_string v1 ^"!="^ aexp_to_string v2
| Inf(v1, v2) -> aexp_to_string v1 ^"<"^ aexp_to_string v2
| InfEqual(v1, v2) -> aexp_to_string v1 ^"<="^ aexp_to_string v2
;;


(* conversion des propositions en chaine de caractere *)
(* vrai *)
prop_to_string tpropTrue;;
(* faux *)
prop_to_string tpropFalse;;

(* vrai et faux *)
prop_to_string tprop2_1;;
(* non vrai *)
prop_to_string tprop2_2;;
(* vrai ou faux  *)
prop_to_string tprop2_3;;
(* faux implique vrai ou faux *)
prop_to_string tprop2_4;;

(* 2 = 4 *)
prop_to_string tprop3_1;;
(* 3+5 = 2*4 *)
prop_to_string tprop3_2;;
(* 2*x = y+1 *)
prop_to_string tprop3_3;;

(*3+x <=4*y *)
prop_to_string tprop4_1;;
(* (5<7) et (8+9 <= 4*5 *)
prop_to_string tprop4_2;;
(* (x=1) implique (y<=0) *)
prop_to_string tprop5;;

(**********  INTERPRETATION ***********)
(* Question 4 : *)
(* fonction qui renvoie la valeur de verite de la formule logique donne en parametre *)
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
(* Evaluation des expressions precedentes*)
let valuation1_4 = [("x", 7);("y", 3) ];;

(* evaluation des proposition avec valuation   *)
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



(**********  SUBSTITUTIONS ***********)

(* Question 6: *)
(* Donction qui permet de remplacer une variable   par une expression arithmetique *)
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
(* affichage des chaines de caracteres des tprop *)
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


(* Liste de propositions  *)
let list_prop = [tpropTrue;tpropFalse;tprop2_1;tprop2_2;tprop2_3;tprop2_4;tprop3_1;tprop3_2;tprop3_3;tprop4_1;tprop4_2];;


(* affichage des formules logiques substituees par les expressions 3*y et k+2 *)
let expx = Mult(Const 3, Var "y");;
let expy = Add(Var "k", Const 2);;

let list_prop = applied "y" expy list_prop;;
let list_prop = applied "x" expx list_prop;;
print_string(printListProp list_prop);;
