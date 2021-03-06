(****** Question 1 *******)
(* type aexpr donnant la syntaxte abstraite des expressions arithmetiques
        - Const pour les nombres 
        - Add pour l addition
        - Mult pour la multiplication
        - Minus pour la soustraction
        - Var pour les variables x, y, z ...
*)
type aexpr = 
Const of int 
| Add of aexpr * aexpr
| Mult of aexpr * aexpr
| Minus of aexpr * aexpr
| Var of string  
;;


(***Question 3: fonction qui transforme une express arithmetiques
                en une chaine de caractere parenthesees***)

let rec aexp_to_string expr =
  match expr with
  | Const x  ->  string_of_int(x)
  | Add (x,y) -> "("^ aexp_to_string x^" + "^ aexp_to_string y^")"
  | Minus (x,y) -> "("^aexp_to_string x^" - "^ aexp_to_string y^ ")"
  | Mult (x,y) -> "("^ aexp_to_string x^" * "^aexp_to_string y^ ")"
  | Var x -> x

;;


(****** Question 2 *******)
(*** utilisation du type aexpr **)
(* Pour 2 *)
let expr1 = Const 2;;
(* Pour 2+3 *)
let expr2 = Add(Const 2, Const 3);;
(* Pour 2-5 *)
let expr3 = Minus(Const 2, Const 5);;
(* Pour 3*6 *)
let expr4 = Mult(Const 3, Const 6);;
(* Pour 2+x *)
let expr5 = Add(Const 2, Var ("x"));;
(* Pour 4*y *)
let expr6 = Mult(Const 4, Var("y"));;
(* Pour 3*x*x *)
let expr7 = Mult(Const 3, Mult(Var("x"), Var("x")));;
(* Pour 5*x+7*y *)
let expr8 = Mult(Const 5, Add(Var("x"), Mult(Const 7, Var ("y"))));;
(* Pour 6*x+5*y*x *)
let expr9 = Mult(Const 6, Add(Var("x"), Mult(Const 5, Mult(Var("y"),Var("x")))));;


(*** Question 3:  affichage des expressions arithmetiques parentheses ***)
aexp_to_string (expr1);;
aexp_to_string (expr2);;
aexp_to_string (expr3);;
aexp_to_string (expr4);;
aexp_to_string (expr5);;
aexp_to_string (expr6);;
aexp_to_string (expr7);;
aexp_to_string (expr8);;
aexp_to_string (expr9);;


(* Question 4: *)
(* Type valuation qui permet de representer les valeurs associees a chaque variable
   qui apparait dans une expression.
   Par exemeple  [("x",5);("y",8)]
   cela va permettre de remplacer tous les x par 5 et tous les y par 8 dans une expression
*)
type valuation = (string * int) list;;

(* Question 5: debut   *)
(* fonction qui permet de remplacer une variable par sa nouvelle valeur (valuation)  *)
let rec get_value var valuation =
   match valuation with
  | [] -> 0
  | (v , value) :: rl -> if (v = var) then value else get_value var rl
;;

(* Question  5: suite*)
(* fonction qui prend en argument une expression arithmetique et une valuation et 
 qui fait le calcul de cette expression avec cette valuation *)
let rec ainterp expr valuation =
  match expr with
  | Const n -> n
  | Mult (e1, e2) -> ainterp e1 valuation * ainterp e2 valuation
  | Add (e1, e2) -> ainterp e1 valuation + ainterp e2 valuation
  | Minus (e1, e2) -> ainterp e1 valuation - ainterp e2 valuation
  | Var var -> get_value var valuation
;;

(*** Question 6:   ***)
(* cration d une valuation *)
let my_valuation : valuation = [("x", 5); ("y", 9)];;

(* Calcul  des exressions avec la valuation [("x", 5); ("y", 9)]  *)

(* Pour 2 *)
ainterp expr1 my_valuation;;
(* Pour 2+3 *)
ainterp expr2 my_valuation;;
(* Pour 2-5 *)
ainterp expr3 my_valuation;;
(* Pour 3*6 *)
ainterp expr4 my_valuation;;
(* Pour 2+x *)
ainterp expr5 my_valuation;;
(* Pour 4*y *)
ainterp expr6 my_valuation;;
(* Pour 3*x*x *)
ainterp expr7 my_valuation;;
(* Pour 5*x+7*y *)
ainterp expr8 my_valuation;;
(* Pour 6*x+5*y*x *)
ainterp expr9 my_valuation;;


(* Question 7  *)
(* fonction qui va remplacer une variable donne en parametre et une aexpr 
et qui renvoie une aexpr dans laquelle toutes les occurrences de la varibales sont 
substituees par l expression arithmetique donne en argument*)
let rec asubst var exp axp =
  match axp with
  | Add (aexpr1, aexpr2) -> Add((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Mult (aexpr1, aexpr2) -> Mult((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Minus (aexpr1, aexpr2) -> Minus((asubst var exp aexpr1), (asubst var exp aexpr2))
  | Var v -> if (v = var) then exp else Var v
  | Const v -> axp
;;
