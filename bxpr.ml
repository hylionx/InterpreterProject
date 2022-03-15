#use "axpr.ml";;

(***
Les expressions booléennes
***)

(***
  bool
***)

(*** Question 1:   ***)

type bexpr = 
  Const of bool
  | Or of bexpr * bexpr
  | End of bexpr * bexpr
  | Not of bexpr
  | Equal of aexpr * aexpr
  | InfEqual of aexpr * aexpr
  ;;

(*** Question 2:   ***)
let bexp1 = Const true;; (* vrai *)

let bexp2_1 = End(Const true, Const false);; (* vrai et faux *)
let bexp2_2 = Not (Const true);; (* non vrai *)
let bexp2_3 = Or(Const true, Const false);; (* vrai ou faux *)

let bexp3_1 = Equal((Const 2), (Const 4));; (* 2 = 4 *)
let bexp3_2 = Equal(Add(Const 3, Const 5), Mult(Const 2, Const 4));; (* 3 + 5 = 2 ∗ 4 *)
let bexp3_3 = Equal(Mult(Const 2, Var "x"), Add(Var "y", Const 1));; (* 2 ∗ x = y + 1 *)

let bexp4_1 = InfEqual(Const 5, Const 7);; (* 5 ≤ 7 *)
let bexp4_2 = InfEqual(Add(Const 8, Const 9), Mult(Const 4, Const 5));; (* (8 + 9 ≤ 4 ∗ 5) *)
let bexp4_3 = InfEqual(Add(Const 3, Var "x"), Mult(Const 4, Var "y"));; (* (3 + x ≤ 4 ∗ y) *)

(*** Question 3:   ***)

let rec bexp_to_string bxpr =
  match bxpr with
  | Const x  ->  string_of_bool(x)
  | Or (x,y) -> "("^ bexp_to_string x^") || ("^ bexp_to_string y^")"
  | End (x,y) -> "("^bexp_to_string x^") && ("^ bexp_to_string y^ ")"
  | Not x -> "!"^ bexp_to_string x
  | Equal (x,y) -> "("^ aexp_to_string x^") == ("^aexp_to_string y^ ")"
  | InfEqual (x,y) -> "("^ aexp_to_string x^") <= ("^aexp_to_string y^ ")"
;;

bexp_to_string bexp1;;
bexp_to_string bexp2_1;;
bexp_to_string bexp2_2;;
bexp_to_string bexp2_3;;
bexp_to_string bexp3_1;;
bexp_to_string bexp3_2;;
bexp_to_string bexp3_3;;
bexp_to_string bexp4_1;;
bexp_to_string bexp4_2;;
bexp_to_string bexp4_3;;


(*** Question 4:   ***)

let opOr x y = 
  match (x, y) with
  | (true, true) -> true
  | (true, false) -> true 
  | (false, true) -> true 
  | (false, false) -> false 
;;

let opAnd x y = 
  match (x, y) with
  | (true, true) -> true
  | (_, _) -> false 
;;

let opNot x = 
  match x with
  | true -> false
  | false -> true
;;

let rec binterp bxpr valu =
  match bxpr with
  | Const x  ->  x
  | Or (x,y) -> opOr (binterp x valu) (binterp x valu)
  | End (x,y) -> opAnd (binterp x valu) (binterp y valu)
  | Not x -> opNot (binterp x valu)
  | Equal (x,y) -> (ainterp x valu) = (ainterp y valu)
  | InfEqual (x,y) ->(ainterp x valu) <= (ainterp y valu)
;;

(*** Question 5:   ***)


let my_valuation_1_2 : valuation = [("x", 7); ("y", 3)];;

(*** interpretations ***)

binterp bexp1 my_valuation_1_2;; (* true *)
binterp bexp2_1 my_valuation_1_2;; (* false *)
binterp bexp2_2 my_valuation_1_2;; (* fasle *)
binterp bexp2_3 my_valuation_1_2;; (* true *)
binterp bexp3_1 my_valuation_1_2;; (* false *)
binterp bexp3_2 my_valuation_1_2;; (* true *)
binterp bexp3_3 my_valuation_1_2;; (* false *)
binterp bexp4_1 my_valuation_1_2;; (* true *) 
binterp bexp4_2 my_valuation_1_2;; (* true *) 
binterp bexp4_3 my_valuation_1_2;; (* true *)

