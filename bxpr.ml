#use "axpr.ml";;

(*** Les expressions booléennes ***)

(*** Question 1:   ***)
(* type bexpr donnant la syntaxte abstraite des expressions booleenne
        - Const pour true ou false
        - Or / And les connnecteurs loiques 
        - Not pour la negation
        - Equals pour l egalite entre deux aexpr 
        - InfEqual pour la relation inferieur ou egale 
*)
type bexpr = 
  Const of bool
  | Or of bexpr * bexpr
  | And of bexpr * bexpr
  | Not of bexpr
  | Equal of aexpr * aexpr
  | InfEqual of aexpr * aexpr
  ;;

  
(*** Question 2:   ***)
(*** definition de plusieurs bexpr **)

(* vrai *)
let bexp1 = Const true;; 
(* vrai et faux *)
let bexp2_1 = And(Const true, Const false);;
(* non vrai *)
let bexp2_2 = Not (Const true);;
(* vrai ou faux *)
let bexp2_3 = Or(Const true, Const false);;
(* 2 = 4 *)
let bexp3_1 = Equal((Const 2), (Const 4));;
(* 3 + 5 = 2 ∗ 4 *)
let bexp3_2 = Equal(Add(Const 3, Const 5), Mult(Const 2, Const 4));;
(* 2 ∗ x = y + 1 *)
let bexp3_3 = Equal(Mult(Const 2, Var "x"), Add(Var "y", Const 1));; 
(* 5 ≤ 7 *)
let bexp4_1 = InfEqual(Const 5, Const 7);;
(* (8 + 9 ≤ 4 ∗ 5) *)
let bexp4_2 = InfEqual(Add(Const 8, Const 9), Mult(Const 4, Const 5));;
(* (3 + x ≤ 4 ∗ y) *)
let bexp4_3 = InfEqual(Add(Const 3, Var "x"), Mult(Const 4, Var "y"));; 


(*** Question 3:   ***)
(* Fonction qui transforme une expression booleenne en une chaine de caractere qui correspond
a l expression booleenne parenthesee *)
let rec bexp_to_string bxpr =
  match bxpr with
  | Const x  ->  string_of_bool(x)
  | Or (x,y) -> "("^ bexp_to_string x^") || ("^ bexp_to_string y^")"
  | And (x,y) -> "("^bexp_to_string x^") && ("^ bexp_to_string y^ ")"
  | Not x -> "!"^ bexp_to_string x
  | Equal (x,y) -> "("^ aexp_to_string x^") == ("^aexp_to_string y^ ")"
  | InfEqual (x,y) -> "("^ aexp_to_string x^") <= ("^aexp_to_string y^ ")"
;;

(* affichage des bexpr parenthese *)
(* vrai *)
bexp_to_string bexp1;;
(* vrai et faux *)
bexp_to_string bexp2_1;;
(* non vrai *)
bexp_to_string bexp2_2;;
(* vrai ou faux *)
bexp_to_string bexp2_3;;
(* 2 = 4 *)
bexp_to_string bexp3_1;;
(* 3 + 5 = 2 ∗ 4 *)
bexp_to_string bexp3_2;;
(* 2 ∗ x = y + 1 *)
bexp_to_string bexp3_3;;
(* 5 ≤ 7 *)
bexp_to_string bexp4_1;;
(* (8 + 9 ≤ 4 ∗ 5) *)
bexp_to_string bexp4_2;;
(* (3 + x ≤ 4 ∗ y) *)
bexp_to_string bexp4_3;;


(*** Question 4:   ***)
(* Fonction qui renvoie la valeur de verite de l operateur ou  *)
let opOr x y = 
  match (x, y) with
  | (true, true) -> true
  | (true, false) -> true 
  | (false, true) -> true 
  | (false, false) -> false 
;;

(* Fonction qui renvoie la valeur de verite de l operateur et  *)
let opAnd x y = 
  match (x, y) with
  | (true, true) -> true
  | (_, _) -> false 
;;

(* Fonction qui renvoie la valeur de verite de l operateur not  *)
let opNot x = 
  match x with
  | true -> false
  | false -> true
;;

(* fonction qui renvoie la valeur de verite de la bxpr en fonction de la valuation donnee en parametre  *)
let rec binterp bxpr valu =
  match bxpr with
  | Const x  ->  x
  | Or (x,y) -> opOr (binterp x valu) (binterp x valu)
  | And (x,y) -> opAnd (binterp x valu) (binterp y valu)
  | Not x -> opNot (binterp x valu)
  | Equal (x,y) -> (ainterp x valu) = (ainterp y valu)
  | InfEqual (x,y) ->(ainterp x valu) <= (ainterp y valu)
;;

(*** Question 5:   ***)
let my_valuation_1_2 : valuation = [("x", 7); ("y", 3)];;

(*** interpretations ***)

(* vrai *)
binterp bexp1 my_valuation_1_2;;
(* vrai et faux *)
binterp bexp2_1 my_valuation_1_2;;
(* non vrai *)
binterp bexp2_2 my_valuation_1_2;;
(* vrai ou faux *)
binterp bexp2_3 my_valuation_1_2;;
(* 2 = 4 *)
binterp bexp3_1 my_valuation_1_2;;
(* 3 + 5 = 2 ∗ 4 *)
binterp bexp3_2 my_valuation_1_2;;
(* 2 ∗ x = y + 1 *)
binterp bexp3_3 my_valuation_1_2;;
(* 5 ≤ 7 *)
binterp bexp4_1 my_valuation_1_2;;
(* (8 + 9 ≤ 4 ∗ 5) *)
binterp bexp4_2 my_valuation_1_2;;
(* (3 + x ≤ 4 ∗ y) *)
binterp bexp4_3 my_valuation_1_2;; 

(* fonction qui supstitue une variable par une boolean   *)
let rec bsubst var exp bxp =
  match bxp with                     
  | Const _  ->  bxp
  | Or (bxp1,bxp2) -> Or((bsubst var exp bxp1), (bsubst var exp bxp2))
  | And (bxp1,bxp2) -> And((bsubst var exp bxp1), (bsubst var exp bxp2))
  | Not bxp1 -> Not(bsubst var exp bxp1)
  | Equal (bxp1,bxp2) -> Equal((asubst var exp bxp1), (asubst var exp bxp2))
  | InfEqual (bxp1,bxp2) ->InfEqual((asubst var exp bxp1), (asubst var exp bxp2))
;;
