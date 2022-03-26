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














let rec apply_hoare_tactic hoare_goal tactic =
  let (context, conclusion) = hoare_goal in (
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
      (*
  | HRepeat s -> 
  (
    failwith("can't use HRepeat")
  )
       *)
      | (HSEq prog, HoareConclusion (Hoare(precond, Seq(prog1, prog2), postcond))) -> [
          (context, HoareConclusion (Hoare(precond, prog1, prog)));
          (context, HoareConclusion (Hoare(prog, prog2, postcond)))
        ]
      | (HSEq p, _) -> failwith("Error HSEq, can't use this tactis")

      | (HCons(cons_pre, cons_post), HoareConclusion (Hoare(precond, prog, postcond))) ->
         let answer = ref [] in
         if cons_post <> postcond
         then answer := ([], PropConclusion(Implied(cons_post, postcond)))::!answer;
         answer := ([], HoareConclusion (Hoare(cons_pre, prog, cons_post)))::!answer;
         if cons_pre <> precond
         then answer := ([], PropConclusion(Implied(cons_pre, precond)))::!answer;
         !answer
         
      | _ -> failwith("Error, unknown tactic")
    )
;;

let rec apply_prop_tactic prop_goal tactic =
  let (context, conclusion) = prop_goal in (
      match tactic with
        
        And_Intro -> (
        match conclusion with
          PropConclusion (And(p, q)) ->
           [ (context, PropConclusion p ) ; (context, PropConclusion q ) ]
        | _ -> failwith("Error And_Intro, can't use this tactis")
      )

                   
      | Or_Intro_1 -> (
        match conclusion with
          PropConclusion (Or(p, q)) -> [(context, PropConclusion p)]
        | _ -> failwith("Error Or_Intro_1, can't use this tactis")
      )

                    
      | Or_Intro_2 -> (
        match conclusion with
          PropConclusion (Or(p, q)) -> [(context, PropConclusion q)]
        | _ -> failwith("Error Or_Intro_2, can't use this tactis")
      )


                    
      | Impl_Intro -> (
        match conclusion with
          PropConclusion (Implied(p, q)) -> [((fresh_ident (), p)::context, PropConclusion q)]
        | _ -> failwith("Error Impl_Intro, can't use this tactis")
      )

                    
      | Not_Intro -> (
        match conclusion with
          PropConclusion (Not(p)) -> [((fresh_ident (), p)::context, PropConclusion(Prop(Const false)))]
        | _ -> failwith("Error Not_Intro, can't use this tactis") 
      )

                   
      | And_Elim_1 sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), p)::context, conclusion)]
          | _ -> failwith("Error And_Elim_1, can't use this tactis") 
        )
      )
                          
                          
      | And_Elim_2 sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), q)::context, conclusion)]
          | _ -> failwith("Error And_Elim_2, can't use this tactis") 
        )
      )
                          
                          
      | Or_Elim sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            Or(p, q) -> [((fresh_ident(), p)::context, conclusion); ((fresh_ident(), q)::context, conclusion)]
          | _ -> failwith("Error Or_Elim, can't use this tactis") 
        )
      )

                       
      | Impl_Elim (sgoal1, sgoal2) -> (
        let hyp1 = get_tprop_in_context context sgoal1
        and hyp2 = get_tprop_in_context context sgoal2 in
        (
          match hyp1 with
            Implied(p, q) -> if p = hyp2
                             then [((fresh_ident(), q)::context, conclusion)]
                             else failwith("Error Impl_Elim, " ^ sgoal1 ^ " don't match with " ^ sgoal2) 
                           
          | _ -> failwith("Error Impl_Elim, can't use this tactis") 
        ) 
      )

                                    
      | Not_Elim (sgoal1, sgoal2) ->  (
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

                                    
      | Exact sgoal -> (
        match conclusion with
          PropConclusion (prop) -> 
           let hyp = get_tprop_in_context context sgoal in
           if hyp = prop
           then  []
           else failwith("Error Exact, don't match goal")
        | _ -> failwith("Error Exact, can't use this tactis") 
      )
                     
      | Assume prop -> ([((fresh_ident (), prop)::context, conclusion)])

      | Admit -> (
        match conclusion with
        | PropConclusion(prop) -> (
          match prop with
          | Prop (_)
            | Equal(_, _)
            | InfEqual(_, _) -> []
          | _ -> failwith("Error Admit, can't use this tactis") 
        )
        | _ -> failwith("Error Admit, can't use this tactis") 
      ) 
               
      | _ -> failwith("Error, unknown tactic")
    )
;;




let apply_tactic goal tactic =
  match goal with
    (_, HoareConclusion(_)) -> apply_hoare_tactic goal tactic
  | (_, PropConclusion(_)) -> apply_prop_tactic goal tactic
;;

let rec apply_tactics_aux tactics goals_list =
  
  match tactics with
  | [] -> []
  | head::tail -> (
    
    match goals_list with
    | [] -> []
    | first_goal::rest_goals -> (
      print_endline "\n__________________________________________________________________\n";
      print_goal (first_goal);
      let new_goals = apply_tactic first_goal head in
      apply_tactics_aux tail (new_goals@rest_goals)
    )
                              
  )
;;

let apply_tactics tactics goal = let _ = reset () in apply_tactics_aux tactics [goal];;


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

let context_1 = [];;
let conclusion_1 = PropConclusion prop;;
let goal_1 = ( context_1, conclusion_1 );;

let tactics = [
    Impl_Intro;
    And_Intro;
    Impl_Intro;
    Assume (Or(p, q));
    Impl_Elim ("H3", "H1");
    Exact "H3";
    Or_Intro_2;
    Exact "H1";
    Impl_Intro;
    Assume (Or(p, q));
    Impl_Elim ("H1", "H6");
    Exact "H7";
    Or_Intro_2;
    Exact "H5"
  ]
;;

apply_tactics tactics goal_1;;


(* Question 4; *)

(* {x = 2} skip {x = 2} *)
let hoare_conclusion_1 =  HoareConclusion (
                              Hoare (
                                  Equal(Var("x"), Const(2)), 
                                  Skip, 
                                  Equal(Var("x"), Const(2))
                                )
                            ) 
;;
apply_tactics [HSkip] ([], hoare_conclusion_1);;



(*{y + 1 < 4} y := y + 1 {y < 4} *)

let hoare_conclusion_2 =  HoareConclusion (
                              Hoare (
                                  InfEqual(Add(Var "y" , Const 1), Const 4), 
                                  Affect("y", Add(Var "y" , Const 1)), 
                                  InfEqual(Var"y", Const 4)
                                )
                            ) 
;;
apply_tactics [HAssign] ([], hoare_conclusion_2);;


(* • {y = 5} x := y + 1 {x = 6} *)

let hoare_conclusion_3 =  HoareConclusion (
                              Hoare (
                                  Equal(Var "y", Const 5), 
                                  Affect("x", Add(Var "y", Const 1)), 
                                  Equal(Var "x", Const 6)
                                )
                            ) 
;;

let hoare_tactics_1 = [
    HCons(Equal(Add(Var "y", Const 1), Const 6), Equal(Var "x", Const 6));
    Impl_Intro;
    Admit; 
    HAssign
  ]
;;

apply_tactics hoare_tactics_1 ([], hoare_conclusion_2);;
