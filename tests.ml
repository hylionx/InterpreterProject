#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;

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





#use "tactic.ml";;


(* 
************************************************************
                        TP1 exo1
************************************************************

Lemma ex1 (P Q: Prop) : P -> (Q -> (P /\ Q)).
Proof.
  Impl_Intro.
  Impl_Intro.
  And_Intro.
  exact H.
  exact H0.
Qed.
 *)


let p = Prop(Const true);;
let q = Prop(Const false);;

let prop = Implied( 
               p,
               Implied(
                   q,
                   And (p, q)
                 )
             )
;;


let context_1 = [];;
let conclusion_1 = [prop];;
let goal_1 = ContextTprop ( context_1, conclusion_1 );;

print_goal goal_1;;

let goal_1_step_1 = apply_tactic goal_1 Impl_Intro;;
print_goal goal_1_step_1;;

let goal_1_step_2 = apply_tactic goal_1_step_1 Impl_Intro;;
print_goal goal_1_step_2;;

let goal_1_step_3 = apply_tactic goal_1_step_2 And_Intro;;
print_goal goal_1_step_3;;

let goal_1_step_4 = apply_tactic goal_1_step_3 (Exact "H16");;
print_goal goal_1_step_4;;

let goal_1_step_5 = apply_tactic goal_1_step_4 (Exact "H15");;
print_goal goal_1_step_5;;




let tactics = [
    Impl_Intro;
    Impl_Intro;
    And_Intro;
    (Exact "H2");
    (Exact "H3")
  ]
;;


print_goal (apply_tactics goal_1 tactics);;

