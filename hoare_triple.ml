#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;

(*question 8*)
(* type hoare_triple qui correspond au triple de hoare
qui est definit par un triplet dun tporp, un prog et un autre tprop *)
type hoare_triple = 
  Hoare of  tprop * prog * tprop
;;

(* question 9 *)

(* {x=2} skip {x=2} *)
let hoare1: hoare_triple = Hoare ( Equal(Var "x", Const 2),
                                   Skip,
                                   Equal(Var "x", Const 2))
;;

(* {x=2} x := 3 {x <= 3} *)
let hoare2: hoare_triple = Hoare( Equal(Var "x", Const 2),
                                  Affect("x", Const 3), 
                                  InfEqual(Var "x", Const 3)
                             )
;;

(* {True} if x <= 0 then r := 0-x else r := x {0 <= r } *)
let hoare3: hoare_triple = Hoare (Prop (Const true),
                                  Cond(
                                      InfEqual(Var "x", Const 0),
                                      Affect("r", Minus(Const 0, Var "x")),
                                      Affect("r", Var "x")),
                                  InfEqual(Const 0, Var "r")              
                             )
;;


(* {in = 5 et out = 1} fact {in = 0 et out = 120} *)
let hoare4: hoare_triple = Hoare (And( Equal(Var "in", Const 5), Equal(Var "out", Const 1)),
                                  fact 5,
                                  And( Equal(Var "in", Const 0), Equal(Var "out", Const 120))
                             )
;;


(* question 10 *)
(* permet de verifier  si un troplet est valide pour la valuation donne en argument  *)
let rec htvalid_test hoare_triple valuation =
  match hoare_triple with
    Hoare (precondition, prog, postcondition) -> (pinterp precondition valuation) &&
                                                   (pinterp postcondition (exec prog valuation))
                                               
                                               
;;

(* affiche le triple de hoare en chaine de caractere *)
let rec triple_to_string (precondition, prog, postcondition) = 
    "{ " ^ (prop_to_string precondition) ^ " }\n"
    ^ "\t" ^ (prog_to_string prog) ^ "\n"
    ^ "{ " ^ (prop_to_string postcondition) ^ " }\n"
;;


let rec hoare_triple_to_string hoare_triple = 
  match hoare_triple with
  | Hoare (precondition, prog, postcondition) ->  triple_to_string (precondition, prog, postcondition)
;;

   


(***** TEST ******)
let valuation1 =[("x", 2)];;
htvalid_test hoare1 valuation1;;

  
  

  
