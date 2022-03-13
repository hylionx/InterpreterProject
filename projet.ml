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
  | (v , value) :: rl -> if (v = var) then value else get_value var rl
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


(* 1.3.1 Syntaxe abstraite  *) 

(* Question 1 *)
type prog = 
  Repeat of aexpr * prog * prog 
  | Skip 
  | Affect of string * aexpr * prog
  | Cond of bexpr * prog * prog * prog
;;

(* Question 2 *)

let prog1 = Affect("y", Const 7, Skip);; (* y := 7 *)

let prog2 = Affect("z", Add(Const 3, Const 4),
            (Affect("x", Mult(Const 2, Var "x"),
            Skip)));;
(* z := 3 + 4 ; x := 2* x *)

let prog3 = Affect("n", Const 3,
            (Cond(
                InfEqual(Var "n", Const 4),
                Affect("n", Add(Mult(Const 2, Var "n"), Const 3), Skip),
                Affect("n", Add(Var "n", Const 1), Skip),
            Skip)));;
(* n := 3; if (n <= 4) then n:= 2*n+3 else n:= n+1 *)

let prog4 = Repeat(Const 10, Affect("x", Add(Var "x", Const 1), Skip),
            Skip);;
(* repeat 10 do x := x+1 od *)

(* Question 3 *)
let rec make_tabs number =
  if number = 0
  then ""
  else"\t" ^ make_tabs (number - 1)
;;

let rec prog_to_string_aux prog tabs =
  match prog with
   |Repeat (x,y,suite) ->
     make_tabs tabs ^ "repeat "^ aexp_to_string x ^" do\n"
     ^ prog_to_string_aux y (tabs + 1) ^ "od"
     ^ prog_to_string_aux suite tabs
   |Skip -> ""
   |Affect(x,y,Skip) ->
     make_tabs tabs ^ x^" := "^ aexp_to_string y ^ "\n"
   |Affect(x,y,suite) ->
     make_tabs tabs ^ x^" := "^ aexp_to_string y ^ " ;\n"
     ^ prog_to_string_aux suite tabs
   |Cond(x,y,Skip,suite) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n "
     ^ prog_to_string_aux suite tabs ^""
   |Cond(x,y,z,suite) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n"
     ^ make_tabs tabs ^"else {\n"
     ^ prog_to_string_aux z (tabs + 1)
     ^ make_tabs tabs ^"}\n "
     ^ prog_to_string_aux suite tabs
;;

let prog_to_string prog =
  prog_to_string_aux prog 0
;;

print_string (prog_to_string prog1);;
print_string (prog_to_string prog2);;
print_string (prog_to_string prog3);;
print_string (prog_to_string prog4);;

(*******Interpretation ******)
(* Question 4 *)

let rec selfcompose func n =
  match n with
  | 0 -> fun v -> v
  | _ -> fun v -> func (selfcompose func (n-1) v) 
;;

(* Question 5 *)
let plus2 x =  x + 2;;

let f = selfcompose plus2 10 ;;
let calcul1 = f 0;;
