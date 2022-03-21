#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;

(*question 8*)
type hoare_triple = 
 Hoare of  tprop * prog * tprop
;;

  (* question 9 *) 
let hoare1: hoare_triple = Hoare ( Equal(Var "x", Const 2),
               Skip,
               Equal(Var "x", Const 2))
;;

(* {x=2} skip {x=2} *)

let hoare2: hoare_triple = Hoare( Equal(Var "x", Const 2),
               Affect("x", Const 3, Skip),
               InfEqual(Var "x", Const 3)
                             )
;;

(* {x=2} x := 3 {x <= 3} *)

let hoare3: hoare_triple = Hoare (Prop (Const true),
                Cond(
                InfEqual(Var "x", Const 0),
                Affect("r", Minus(Const 0, Var "x"), Skip),
                Affect("r", Var "x", Skip),
                Skip),
                InfEqual(Const 0, Var "r")              
                             )
;;

(* {True} if x <= 0 then r := 0-x else r := x {0 <= r } *)


let hoare4: hoare_triple = Hoare (And( Equal(Var "in", Const 5), Equal(Var "out", Const 1)),
              fact,
              And( Equal(Var "in", Const 0), Equal(Var "out", Const 120))
                             )
;;

(* {in = 5 et out = 1} fact {in = 0 et out = 120} *)


let fact v = Affect ("i", Const v,
                   Affect("res", Const 1,
                                 Repeat (Const v,
                                         Affect("res", Mult(Var "res", Var "i"),
                                                Affect("i", Minus(Var "i", Const 1),
                                                       Skip)),
                                         Skip)))
;;

exec (fact 5) [];;

(* question 10 *)
let rec htvalid_test hoare_triple valuation =
  match hoare_triple with
    Hoare (precondition, prog, postcondition) -> (pinterp precondition valuation) &&
                                                 (pinterp postcondition (exec prog valuation))
                                                   
      
;;

(***** TEST ******)
let valuation1 =[("x", 2)];;
htvalid_test hoare1 valuation1;;

;
  
                   

                   
