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

(*let rec apply_hoare_tactic hoare tactic =
match tactic with 
 | HSkip -> 
(
    match goal with
    | ContextHoare (context, HSkip::tail) -> ContextTprop (context, (p)::(q)::tail)
    | _ -> failwith("can't use HSkip")
)
 | HAssign -> 
 (
   failwith("can't use HAssign")
 )
 | HIf -> 
 (
   failwith("can't use HIf")
 )
 | HRepeat s -> 
 (
   failwith("can't use HRepeat")
 )
 | HSEq p -> 
 (
   failwith("can't use HSEq")
 )
 | _ -> 
 (
   failwith("it isn't hoare")
 )

and*)

let rec apply_prop_tactic goal tactic =
  let (context, conclusion) = goal in (
      match tactic with
        
        And_Intro -> (
        match conclusion with
          PropConclusion (And(p, q)) ->
           [ (context, PropConclusion p ) ; (context, PropConclusion q ) ]
        | _ -> failwith("can't use And_Intro")
      )

                   
      | Or_Intro_1 -> (
        match conclusion with
          PropConclusion (Or(p, q)) -> [(context, PropConclusion p)]
        | _ -> failwith("can't use Or_Intro_1") 
      )

                    
      | Or_Intro_2 -> (
        match conclusion with
          PropConclusion (Or(p, q)) -> [(context, PropConclusion q)]
        | _ -> failwith("can't use Or_Intro_2") 
      )


                    
      | Impl_Intro -> (
        match conclusion with
          PropConclusion (Implied(p, q)) -> [((fresh_ident (), p)::context, PropConclusion q)]
        | _ -> failwith("can't use Impl_Intro") 
      )

                    
      | Not_Intro -> (
        match conclusion with
          PropConclusion (Not(p)) -> [((fresh_ident (), p)::context, PropConclusion(Prop(Const false)))]
        | _ -> failwith("can't use Not_Intro") 
      )

                   
      | And_Elim_1 sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), p)::context, conclusion)]
          | _ -> failwith("can't use And_Elim_1") 
        )
      )
                          
                          
      | And_Elim_2 sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            And(p, q) -> [((fresh_ident (), q)::context, conclusion)]
          | _ -> failwith("can't use And_Elim_2") 
        )
      )
                          
                          
      | Or_Elim sgoal -> (
        let hypothese = get_tprop_in_context context sgoal in
        (
          match hypothese with
            Or(p, q) -> [((fresh_ident(), p)::context, conclusion); ((fresh_ident(), q)::context, conclusion)]
          | _ -> failwith("can't use Or_Elim") 
        )
      )

                       
      | Impl_Elim (sgoal1, sgoal2) -> (
        let hyp1 = get_tprop_in_context context sgoal1
        and hyp2 = get_tprop_in_context context sgoal2 in
        (
          match hyp1 with
            Implied(p, q) -> if p = hyp2
                             then [((fresh_ident(), q)::context, conclusion)]
                             else failwith(sgoal1 ^ " don't match with " ^ sgoal2) 
                           
          | _ -> failwith("Error, hypothesis does not match") 
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
             else failwith(sgoal1 ^ " don't match with " ^ sgoal2) 
            
          | _ -> failwith("can't use Not_Elim") 
        )
      )

                                    
      | Exact sgoal -> (
        match conclusion with
          PropConclusion (prop) -> 
           let hyp = get_tprop_in_context context sgoal in
           if hyp = prop
           then  []
           else failwith("don't match goal")
        | _ -> failwith("can't use Exact")
      )
                     
      | Assume prop -> ([((fresh_ident (), prop)::context, conclusion)])
                     
      | _ -> failwith("it isn't hoare")
    )
;;




let apply_tactic goal tactic =
  match goal with
    (_, HoareConclusion(_)) -> failwith("non") (*apply_hoare_tactic goal tactic *)
  | (_, PropConclusion(_)) -> apply_prop_tactic goal tactic
;;


(* Question 3; *)

let p = Prop(Const true);;
let q = Prop(Const false);;
let r = Prop(Const true);;

let prop = Implied( 
               Or(p, Implied(q, r) ),
               And(
                   (Implied(p, r)),
                   (Implied(q, r))
                 ) 
             )
;;

let context_1 = [];;
let conclusion_1 = PropConclusion prop;;
let goal_1 = ( context_1, conclusion_1 );;

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
      apply_tactics_aux tail  new_goals@rest_goals
    )

  )
;;

let apply_tactics tactics goal =  apply_tactics_aux tactics [goal];;
     
let p_or_q = Or(p, q);;

let tactics = [
    Impl_Intro;
    And_Intro;
    Impl_Intro;
    Assume p_or_q;
    Impl_Elim "H 0" "H 2";
    Exact "H 3";
    Or_Intro_2;
    Exact "H 1";
    Impl_Intro;
    Assume p_or_q;
    Impl_Elim "H 0" "H 2";
    Exact "H 3";
    Or_Intro_2;
    Exact "H 1"
  ]
;;

print_goal (apply_tactics goal_1 tactics);;

