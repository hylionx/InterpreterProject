#use "goal.ml"
  
type tactic = 
And_Intro
|Or_Intro_1
|Or_Intro_2
|Impl_Intro
|Not_Intro 
|And_Elim_1 of string
|And_Elim_2 of string
|Or_Elim of goal
|Impl_Elim of goal
|Not_Elim of goal
|Exact of goal
|Assume 
|HSkip
|HAssign
|HIf
|HRepeat of string
|HCons of tprop
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
  | (str, prop)::taill ->
     if str = sgoal
     then prop
     else get_tprop_in_context tail sgoal
;;


let rec apply_hoare_tactic hoare tactic =
match tactic with
  Assume -> 
 | HSkip -> 
 | HAssign ->
 | HIf ->
 | HRepeat s ->
 | HCons p ->
 | HSEq p ->
 | _ -> 

and rec apply_prop_tactic goal tactic =
  match tactic with
    And_Intro -> {
      match goal with
        ContextTprop (context, And(p, q)::tail ) -> ContextTprop (context, (p)::(q)::tail)
      | _ -> failwith("can't use And_Intro")
    }
  | Or_Intro_1 -> {
      match goal with
       ContextTprop (context, Or(p, q)::tail ) -> ContextTprop (context, (q)::Or(p, q)::tail)
      | _ -> failwith("can't use Or_Intro_1") 
    }
  | Or_Intro_2 -> {
      match goal with
       ContextTprop (context, Or(p, q)::tail ) -> ContextTprop (context, (p)::Or(p, q)::tail)
      | _ -> failwith("can't use Or_Intro_2") 
    }
   | Impl_Intro -> {
      match goal with
       ContextTprop (context, Impl(p, q)::tail ) -> ContextTprop ((fresh_ident (), p)::context, q::tail)
      | _ -> failwith("can't use Impl_Intro") 
    }
   | Not_Intro  -> print_line("la m�re a hugo")
   | And_Elim_1 sgoal -> {
      match goal with
        ContextTprop (context, conclusion) ->
         let hypothese = get_tprop_in_context context sgoal in
         {
           match hypothese with
             And(p, q) -> ContextTprop ((fresh_ident (), p)::context, conclusion)
           | _ -> failwith("can't use And_Elim_1") 
         }
      | _ -> failwith("can't use And_Elim_1") 
    }
   | And_Elim_2 sgoal -> {
      match goal with
        ContextTprop (context, conclusion) ->
         let hypothese = get_tprop_in_context context sgoal in
         {
           match hypothese with
             And(p, q) -> ContextTprop ((fresh_ident (), q)::context, conclusion)
           | _ -> failwith("can't use And_Elim_2") 
         }
      | _ -> failwith("can't use And_Elim_2") 
    }
   | Or_Elim goal ->
   | Impl_Elim goal ->
   | Not_Elim goal ->
   | Exact goal ->
   | _ -> 
;;

let apply_tactic goal tactic =
  match goal with
    ContextHoare (_, _) -> apply_hoare_tactic goal tactic
  | ContextTprop (_, _) -> apply_prop_tactic goal tactic
;;
