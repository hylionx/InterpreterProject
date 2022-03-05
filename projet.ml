#load "str.cma";;


(*
garbage 


let replace var replace_by input = Str.global_replace (Str.regexp_string var) replace_by input;;

replace "x" "5" (aexp_to_string (expr9));;

let rec replace_all my_valuation expr =
  match my_valuation with
  | [] -> expr
  | (var , replace_by) :: rl -> replace_all rl (replace var (string_of_int replace_by) expr)
;;

replace_all  my_valuation (aexp_to_string (expr9));;
 *)





(****** Question 1 *******)

type aexpr = 
Const of int 
| Add of aexpr * aexpr
| Mult of aexpr * aexpr
| Minus of aexpr * aexpr
| Var of string  
;;


(*** Ajouter en plus ce n'est pas demand� ****)
let rec calcul = function
  | Const n -> n
  | Mult (e1, e2) -> calcul e1 * calcul e2
  | Add (e1, e2) -> calcul e1 + calcul e2
  | Minus (e1, e2) -> calcul e1 - calcul e2
  | Var n -> int_of_string(n)
;; 


(**Question 3: fonction qui transforme une express arithm
en une chaine de caractere parenthesees**)

let rec aexp_to_string expr =
  match expr with
  | Const x  ->  string_of_int(x)
  | Add (x,y) -> "("^ aexp_to_string x^" + "^ aexp_to_string y^")"
  | Minus (x,y) -> "("^aexp_to_string x^" - "^ aexp_to_string y^ ")"
  | Mult (x,y) -> "("^ aexp_to_string x^" * "^aexp_to_string y^ ")"
  | Var x -> x

;;


(****** Question 2 *******)
let expr1 = Const 2;; (** Pour 2 **)
let expr2 = Add(Const 2, Const 3);; (** Pour 2+3**)
let expr3 = Minus(Const 2, Const 5);; (** Pour 2-5 **)
let expr4 = Mult(Const 3, Const 6);; (** Pour 3*6 **)
let expr5 = Add(Const 2, Var ("x"));;(** Pour 2+x **)
let expr6 = Mult(Const 4, Var("y"));;(** Pour 4*y **)
let expr7 = Mult(Const 3, Mult(Var("x"), Var("x")));;(** Pour 3*x*x **)
let expr8 = Mult(Const 5, Add(Var("x"), Mult(Const 7, Var ("y"))));;(** Pour 5*x+7*y**)
let expr9 = Mult(Const 6, Add(Var("x"), Mult(Const 5, Mult(Var("y"),Var("x")))));;(** Pour 6*x+5*y*x**)

calcul expr3;;

(** Question 3:  affichage des expressions arithmetiques parentheses **)
aexp_to_string (expr1);;
aexp_to_string (expr2);;
aexp_to_string (expr3);;
aexp_to_string (expr4);;
aexp_to_string (expr5);;
aexp_to_string (expr6);;
aexp_to_string (expr7);;
aexp_to_string (expr8);;
aexp_to_string (expr9);;




(** Question 4:   **)
type valuation = (string * int) list;;

(** Question 5:   **)

let rec get_value var valuation =
   match valuation with
  | [] -> 0
  | (v , value) :: rl -> if (v = var) then value else get_value_of_var var rl
;;

let rec ainterp expr valuation =
  match expr with
  | Const n -> n
  | Mult (e1, e2) -> ainterp e1 valuation * ainterp e2 valuation
  | Add (e1, e2) -> ainterp e1 valuation + ainterp e2 valuation
  | Minus (e1, e2) -> ainterp e1 valuation - ainterp e2 valuation
  | Var var -> get_value var valuation
;;

(** Question 6:   **)

let my_valuation : valuation = [("x", 5); ("y", 9)];;

ainterp expr1 my_valuation;;
ainterp expr2 my_valuation;;
ainterp expr3 my_valuation;;
ainterp expr4 my_valuation;;
ainterp expr5 my_valuation;;
ainterp expr6 my_valuation;;
ainterp expr7 my_valuation;;
ainterp expr8 my_valuation;;
ainterp expr9 my_valuation;;


(***test commit *****)