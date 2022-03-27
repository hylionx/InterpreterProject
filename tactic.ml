#use "goal.ml";;


type tactic = 
  And_Intro
|Or_Intro_1
|Or_Intro_2
|Impl_Intro
|Not_Intro 
|And_Elim_1 of string
|And_Elim_2 of string
|Or_Elim of string
|Impl_Elim of string * string
|Not_Elim of string * string
|Exact of string
|Assume of tprop
|Admit
|HSkip
|HAssign
|HIf
|HRepeat of string
|HCons of tprop * tprop
|HSEq of tprop
;;

(* Question 1: *)

let rec bool2prop e =
  match e with
    Const cst -> Prop e
  | Or (b1, b2) -> Or (bool2prop b1 ,bool2prop b2)
  | And (b1, b2) -> And (bool2prop b1,bool2prop b2)
  | Not b -> Not (bool2prop b)
  | Equal (e1, e2) -> Equal(e1, e2)
  | InfEqual (e1, e2) -> InfEqual(e1, e2)
;;

(* Question 2 : *)

let rec get_tprop_in_context context sgoal =
  match context with
    [] -> failwith("can't find " ^sgoal ^" into the context list")
  | (str, prop)::tail ->
     if str = sgoal
     then prop
     else get_tprop_in_context tail sgoal
;;

let rec remove_tprop_in_context context sgoal =
  match context with
  | (str, prop)::tail ->
     if str = sgoal
     then tail
     else (str, prop)::(remove_tprop_in_context tail sgoal)
  | [] -> failwith("can't find " ^sgoal ^" into the context list")
;;

let rec change_tprop_in_context context sgoal new_prop =
  match context with
    [] -> failwith("can't find " ^sgoal ^" into the context list")
  | (str, prop)::tail ->
     if str = sgoal
     then (sgoal, new_prop)::tail
     else change_tprop_in_context tail sgoal new_prop
;;














let rec apply_hoare_tactic context conclusion tactic =
  match (tactic, conclusion)  with 
  | (HSkip, HoareConclusion (Hoare((precond, Skip, postcond )))) when (precond = postcond) -> []
  | (HSkip, _) -> failwith("Error HSkip, can't use this tactis")
                
  | (HAssign, HoareConclusion (Hoare((precond, Affect (var, value), postcond )))) when (precond = psubst var value postcond) -> []
  | (HAssign, _) -> failwith("Error HAssign, can't use this tactis")

  | (HIf, HoareConclusion (Hoare((precond, Cond(bexp, prog_then, prog_else), postcond )))) -> [
      (context, HoareConclusion (Hoare(And(precond, (bool2prop bexp)), prog_then, postcond)));
      (context, HoareConclusion (Hoare(And(precond, Not((bool2prop bexp))), prog_else, postcond)))
    ]
  | (HIf, _) -> failwith("Error HIf, can't use this tactis")
              
  | (HRepeat i, HoareConclusion (Hoare((precond, Repeat (e, prog), And(p, _) )))) when ((psubst i (Const 1) p) = precond) -> [
        context, HoareConclusion (
                     Hoare(
                         And(p, InfEqual(Var i, e)),
                         prog,
                         psubst i (Add(Var "i", Const 1)) p
                       )
                   )
      ]  
  | (HRepeat i, _) -> failwith("Error HRepeat, can't use this tactis")

  | (HCons(cons_pre, cons_post), HoareConclusion (Hoare(precond, prog, postcond))) ->
     let answer = ref [] in
     if cons_post <> postcond
     then  answer := ([], PropConclusion(Implied(cons_post, postcond)))::!answer;
     answer := ([], HoareConclusion (Hoare(cons_pre, prog, cons_post)))::!answer;
     if cons_pre <> precond
     then answer := ([], PropConclusion(Implied(cons_pre, precond)))::!answer;
     !answer

  | (HCons(cons_pre, cons_post), _) -> failwith("Error HCons, can't use this tactis")

  | (HSEq prog, HoareConclusion (Hoare(precond, Seq(prog1, prog2), postcond))) -> [
      (context, HoareConclusion (Hoare(precond, prog1, prog)));
      (context, HoareConclusion (Hoare(prog, prog2, postcond)))
    ]
  | (HSEq p, _) -> failwith("Error HSEq, can't use this tactis")
                 
  | _ -> failwith("Error, unknown tactic")
;;

let rec apply_prop_tactic context conclusion tactic =
    match (tactic, conclusion) with
      | (And_Intro, PropConclusion (And(p, q))) -> [ (context, PropConclusion p ) ; (context, PropConclusion q ) ]
      | (And_Intro, _) -> failwith("Error And_Intro, can't use this tactis")
                  
      | (Or_Intro_1, PropConclusion (Or(p, q))) -> [(context, PropConclusion p)]
      | (Or_Intro_1, _) -> failwith("Error Or_Intro_1, can't use this tactis")
    
      | (Or_Intro_2, PropConclusion (Or(p, q))) -> [(context, PropConclusion q)]
      | (Or_Intro_2, _) -> failwith("Error Or_Intro_2, can't use this tactis")
                  
      | (Impl_Intro, PropConclusion (Implied(p, q))) -> [((fresh_ident (), p)::context, PropConclusion q)]
      | (Impl_Intro, _) -> failwith("Error Impl_Intro, can't use this tactis")
                  
      | (Not_Intro, PropConclusion (Not(p))) -> [((fresh_ident (), p)::context, PropConclusion(Prop(Const false)))]
      | (Not_Intro, _) -> failwith("Error Not_Intro, can't use this tactis") 
                  
      | (And_Elim_1 sgoal, _) -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), p)::context, conclusion)]
          | _ -> failwith("Error And_Elim_1, can't use this tactis") 
        )
      )
                          
      | (And_Elim_2 sgoal, _) -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), q)::context, conclusion)]
          | _ -> failwith("Error And_Elim_2, can't use this tactis") 
        )
      )
                          
      | (Or_Elim sgoal, _) -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            Or(p, q) -> [((fresh_ident(), p)::context, conclusion); ((fresh_ident(), q)::context, conclusion)]
          | _ -> failwith("Error Or_Elim, can't use this tactis") 
        )
      )
                      
      | (Impl_Elim (sgoal1, sgoal2), _) -> (
        let hyp1 = get_tprop_in_context context sgoal1
        and hyp2 = get_tprop_in_context context sgoal2 in
        (
          match hyp1 with
            Implied(p, q) -> 
              if p = hyp2
              then [((fresh_ident(), q)::context, conclusion)]
              else failwith("Error Impl_Elim, " ^ sgoal1 ^ " don't match with " ^ sgoal2) 
                          
          | _ -> failwith("Error Impl_Elim, can't use this tactis") 
        ) 
      )
                                    
      | (Not_Elim (sgoal1, sgoal2), _) ->  (
        let hyp1 = get_tprop_in_context context sgoal1
        and hyp2 = get_tprop_in_context context sgoal2 in
        (
          match hyp1, hyp2 with
            (Not p), q ->
              if p = q
              then  [((fresh_ident (), Prop (Const false))::context, conclusion)]
              else failwith("Error Not_Elim, " ^sgoal1 ^ " don't match with " ^ sgoal2) 
            
          | _ -> failwith("Error Not_Elim, can't use this tactis") 
        )
      )
                                    
      | (Exact sgoal, PropConclusion (prop)) -> 
            let hyp = get_tprop_in_context context sgoal in
              if hyp = prop
              then  []
              else failwith("Error Exact, don't match goal")

      | (Exact sgoal, _) -> failwith("Error Exact, can't use this tactis") 
                    
      | (Assume prop, _) -> ([((fresh_ident (), prop)::context, conclusion)])

      | (Admit, PropConclusion(prop)) -> (
          match prop with
            | Prop (_)
            | Equal(_, _)
            | InfEqual(_, _) -> []
            | _ -> failwith("Error Admit, can't use this tactis with this prop") 
        )
      | (Admit, _) -> failwith("Error Admit, can't use this tactis") 
      
      | _ -> failwith("Error, unknown tactic")
;;




let apply_tactic goal tactic =
  let (context, conclusion) = goal in (
      match conclusion with
      | HoareConclusion(_) -> apply_hoare_tactic context conclusion tactic
      | PropConclusion(_) -> apply_prop_tactic context conclusion tactic
    )
;;

let rec apply_tactics_aux tactics goals_list =
  
  match tactics with
  | [] -> goals_list
  | head::tail -> (
    
    match goals_list with
    | [] -> []
    | first_goal::rest_goals -> (
      print_goal (first_goal);
      print_endline "\n************************************************************************\n\n";
      let new_goals = apply_tactic first_goal head in
      apply_tactics_aux tail (new_goals@rest_goals)
    )
                              
  )
;;

let rec listlength list =
  match list with
    [] -> 0
  | head::tail -> 1 + listlength tail
;;


let apply_tactics tactics goal =
  let _ = reset () in
  let ret = apply_tactics_aux tactics [goal] in
  if ret = []
  then ( print_endline("no more subgoals."); ret )
  else failwith("fail to proof, there still " ^ string_of_int( listlength ret) ^" subgoals")
;;


(* Question 3; *)

(* (P \/ Q => R) => P => R) /\ (Q => R) *)

let p = Prop(Const true);;
let q = Prop(Const false);;
let r = Prop(Const true);;

let prop = Implied(
               Implied ( Or(p, q) , r),
               And(
                   (Implied(p, r)),
                   (Implied(q, r))
                 ) 
             )
;;

let prop_conclusion_1 = PropConclusion prop;;

let tactics = [
    Impl_Intro;
    And_Intro;
    Impl_Intro;
    Assume (Or(p, q));
    Impl_Elim ("H1", "H3");
    Exact "H4";
    Impl_Intro;
    Assume (Or(p, q));
    Impl_Elim ("H1", "H6");
    Exact "H7";
    Or_Intro_2;
    Exact "H5";
    Or_Intro_1;
    Exact "H2";
    Exact "H7"
  ]
;;
apply_tactics tactics ([], prop_conclusion_1 );;


(* Question 4; *)

(* {x = 2} skip {x = 2} *)
(* code coq
Lemma projet1 (x: nat) :
  {{x = 2}}
    Skip
  {{x = 2}}.
Proof.
Hoare_consequence_rule_left with (x = 2).
Hoare_skip_rule.
Qed.
 *)
let hoare_1 = Hoare (
                                  Equal(Var "x", Const 2), 
                                  Skip, 
                                  Equal(Var "x", Const 2)
                );;

let hoare_conclusion_1 =  HoareConclusion (
                             hoare_1
                            ) 
;;

apply_tactics [HSkip] ([], hoare_conclusion_1);;



(* {y + 1 < 4} y := y + 1 {y < 4} *)
(* code coq 
Lemma projet2 (y: nat) :
  {{y + 1 < 4}} 
    y ::= y + 1 
  {{y < 4}}.
Proof.
Hoare_assignment_rule.
Qed.
*)

let hoare_2 = Hoare (
                                  InfEqual(Add(Var "y" , Const 1), Const 4), 
                                  Affect("y", Add(Var "y" , Const 1)), 
                                  InfEqual(Var"y", Const 4)
                                );;

let hoare_conclusion_2 =  HoareConclusion (
                              hoare_2
                            ) 
;;

apply_tactics [HAssign] ([], hoare_conclusion_2);;


(* {y = 5} x := y + 1 {x = 6} *)
(* 
Lemma projet3 (x y: nat) :
  {{y = 5}}
    x ::= y + 1
  {{x = 6}}.
Proof.
Hoare_consequence_rule_left
with (y + 1  = 6).
Impl_Intro.
rewrite H.
reflexivity.
Hoare_assignment_rule.
Qed.
 *)
let hoare_3 = Hoare (
                                  Equal(Var "y", Const 5), 
                                  Affect("x", Add(Var "y", Const 1)), 
                                  Equal(Var "x", Const 6)
                                );;

let hoare_conclusion_3 =  HoareConclusion (
                              hoare_3
                            ) 
;;

let hoare_tactics_3 = [
    HCons(Equal(Add(Var "y", Const 1), Const 6), Equal(Var "x", Const 6));
    Impl_Intro;
    Admit; 
    HAssign
  ]
;;
apply_tactics hoare_tactics_3 ([], hoare_conclusion_3);;



(* {True} z := x; z := z+y; u := z {u = x + y}  *)
(*
(*
{{True}} 
{{x + y = x + y}}
  z ::= x;;
{{z + y = x + y}}
  z ::= z + y;;
{{z = x + y}}
  u ::= z 
{{u = x + y}}.
*)

Lemma projet4 (z u x y: nat) :
{{True}} 
  z ::= x;;
  z ::= z + y;;
  u ::= z 
{{u = x + y}}.
Proof.
Hoare_consequence_rule_left
with (x + y = x + y).
Hoare_sequence_rule with (z = x + y).
Hoare_sequence_rule with (z + y = x + y).
Hoare_assignment_rule.
Hoare_assignment_rule.
Hoare_assignment_rule.
Qed.
 *)
let hoare_4 =Hoare (
                                  Prop (Const true), 
                                  Seq
                                    (
                                      Seq
                                        (
                                          Affect("z", Var "x"), 
                                          Affect("z", Add(Var "z", Var "y"))
                                        ),
                                      Affect("u", Var "z")
                                    ),
                                  Equal(Var "u", Add(Var "x", Var "y"))
                                );;

let hoare_conclusion_4 =  HoareConclusion (
                              hoare_4
                            ) 
;;

let hoare_tactics_4 = [
    HSEq(Equal(Var "z", Add(Var "x", Var "y")));
    HSEq(Equal(Add(Var "z", Var "y"), Add(Var "x", Var "y")));
    HCons(
      Equal(Add(Var "x", Var "y"), Add(Var "x", Var "y")),
      Equal(Add(Var "z", Var "y"), Add(Var "x", Var "y")));
    Impl_Intro;
    Admit;
    HAssign;
    HAssign;
    HAssign
  ]
;;
apply_tactics hoare_tactics_4 ([], hoare_conclusion_4);;



(* {True} if v <= 0 then r := 0-v else r := v {0 <= r}  *)
(* 
(*
{{True}}
  If v <=? 0 
{{0 <= 0- v}}
  Then r ::= 0-v 
{{(0 <= v) /\ (}}
  Else r ::= v 
  Fi
{{(x >= 0 /\ (! (x =? 0)) = false)}}
{{0 <= r}}
*)
Lemma projet5 (v r: nat) :
{{True}}
  If v <=? 0 
  Then r ::= 0-v 
  Else r ::= v 
  Fi
{{0 <= r}}.
Proof.
Hoare_if_rule.
Hoare_consequence_rule_left
with (0 <= (0-v)).
 Hoare_assignment_rule. 
Hoare_consequence_rule_left
with (0 <= v).
Impl_Intro.
And_Elim_2 in H.
bool2Prop in H0. 
lia.
Hoare_assignment_rule.
Qed.
 *)
let hoare_5 =  Hoare (
                   Prop (Const true),
                   Cond (
                       InfEqual (Var "v", Const 0),
                       Affect ("r", Minus (Const 0, Var "v")),
                       Affect ("r", Var "v")
                     ),
                   InfEqual (Const 0, Var "r")
                 );;

let hoare_conclusion_5 =  HoareConclusion (
                             hoare_5
                            ) 
;;

let hoare_tactics_5 = [
    HIf;
    HCons (
        InfEqual(Const 0, Minus (Const 0, Var "v")),
        InfEqual (Const 0, Var "r")
      );
    Impl_Intro;
    And_Intro;
    Admit;
    Admit;
    HAssign;
    HCons (
        InfEqual(Const 0, Var "v"),
        InfEqual (Const 0, Var "r")
      );
    Impl_Intro;
    And_Intro;
    Admit;
    Not_Intro;
    Admit;
    HCons (
        InfEqual(Const 0, Var "v"),
        InfEqual (Const 0, Var "r")
      );
    HAssign;
  ]
;;
apply_tactics hoare_tactics_5 ([], hoare_conclusion_5);;


(* {x = y} repeat 10 do x:= x+1 od {x = y + 10}  *)
let hoare_6 = Hoare (
                                Equal(Var "x", Var "y"), 
                                Repeat(Const 10, Affect ("x", Add(Var "x", Const 1))), 
                                Equal(Var "x", Add(Var "y", Const 10))
                              );;

let hoare_conclusion_6 =  HoareConclusion (
                              hoare_6
                            ) ;;
;;

let hoare_tactics_6 = [
  HCons(
    Equal(Var "x", Minus(Add(Var "y", Const 1), Const 1)),
    And(
      Equal(Var "x", Minus(Add(Var "y", Var "i"), Const 1)),
      Equal(Var "i", Add(Const 10, Const 1))
    )
  );
  Impl_Intro;
  Admit;
  HRepeat("i");
  HCons(
    Equal(Add(Var "x", Const 1), Minus(Add(Var "y", Add(Var "i", Const 1)), Const 1)),
    Equal(Var "x", Minus(Add(Var "y", Add(Var "i", Const 1)), Const 1))
  );
  Impl_Intro;
  And_Intro;
  Admit;
  Admit;
  HAssign;
  Impl_Intro;
  Admit;
];;
apply_tactics hoare_tactics_6 ([], hoare_conclusion_6);;

(* Question 5; *)

let rec htvalid_multiple_test hoare_triple valuations = 
  match valuations with
  | [] -> true
  | head::tail -> (htvalid_test hoare_triple head) && (htvalid_multiple_test hoare_triple tail)
;;



(* exemple 1 *)
htvalid_multiple_test hoare_1 [[("x", 2)]];;


(* exemple 2 *)
htvalid_multiple_test hoare_2 [
    [("y", 2)]; [("y", -2)];
    [("y", -5)]
  ]
;;

(* exemple 3 *)
htvalid_multiple_test hoare_3 [[("y", 5)]];;

(* exemple 4 *)
htvalid_multiple_test hoare_4 [
    [("x", 5);("y", 10)];
    [("x", -5);("y", 10)];
    [("x", -5);("y", 8)];
    [("x", 5);("y", 8)]
  ]
;;

(* exemple 5 *)
htvalid_multiple_test hoare_5 [
    [("v", 2)];
    [("v", -2)]
  ]
;;

(* exemple 6 *)
htvalid_multiple_test hoare_6 [
    [("x", 2);("y", 2)];
    [("x", 5);("y", 5)];
    [("x", 25);("y", 25)];
    [("x", 50);("y", 50)]
  ]
;;
