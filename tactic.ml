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


let rec do_imp_elim context conclusion hyp =
  match hyp with
    Implied(p, q) -> do_imp_elim context (conclusion@[p]) q
  |  _ -> ContextTprop((fresh_ident (), hyp)::context, conclusion)
  ;;


let rec apply_hoare_tactic hoare tactic =
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

and apply_prop_tactic goal tactic =

  match tactic with
    And_Intro -> (
    match goal with
      ContextTprop (context, And(p, q)::tail) -> ContextTprop (context, (p)::(q)::tail)
    | _ -> failwith("can't use And_Intro")
  )
  | Or_Intro_1 -> (
    match goal with
      ContextTprop (context, Or(p, q)::tail ) -> ContextTprop (context, (q)::Or(p, q)::tail)
    | _ -> failwith("can't use Or_Intro_1") 
  )
  | Or_Intro_2 -> (
    match goal with
      ContextTprop (context, Or(p, q)::tail ) -> ContextTprop (context, (p)::Or(p, q)::tail)
    | _ -> failwith("can't use Or_Intro_2") 
  )
  | Impl_Intro -> (
    match goal with
      ContextTprop (context, Implied(p, q)::tail ) -> ContextTprop ((fresh_ident (), p)::context, q::tail)
    | _ -> failwith("can't use Impl_Intro") 
  )
  | Not_Intro  -> failwith("la m�re a hugo, et puis ca sert a rien !")
  | And_Elim_1 sgoal -> (
    match goal with
      ContextTprop (context, conclusion) ->
       let hypothese = get_tprop_in_context context sgoal in
       (
         match hypothese with
           And(p, q) -> ContextTprop ((fresh_ident (), p)::context, conclusion)
         | _ -> failwith("can't use And_Elim_1") 
       )
    | _ -> failwith("can't use And_Elim_1") 
  )
  | And_Elim_2 sgoal -> (
    match goal with
      ContextTprop (context, conclusion) ->
       let hypothese = get_tprop_in_context context sgoal in
       (
         match hypothese with
           And(p, q) -> ContextTprop ((fresh_ident (), q)::context, conclusion)
         | _ -> failwith("can't use And_Elim_2") 
       )
    | _ -> failwith("can't use And_Elim_2") 
  )
  | Or_Elim sgoal -> (
    match goal with
      ContextTprop (context, conclusion) ->
       let hypothese = get_tprop_in_context context sgoal in
       (
         match hypothese with
           Or(p, q) -> ContextTprop (( change_tprop_in_context context sgoal p), Or(q, p)::conclusion)
         | _ -> failwith("can't use Or_Elim") 
       )
    | _ -> failwith("can't use Or_Elim") 
  )
  | Impl_Elim (sgoal1, sgoal2) -> (
    match goal with
      ContextTprop (context, conclusion) ->
       let hyp1 = get_tprop_in_context context sgoal1
       and hyp2 = get_tprop_in_context context sgoal2 in
       (
         match hyp1 with
           Implied(p, q) -> if p = hyp2
                         then do_imp_elim context conclusion hyp2
                         else failwith(sgoal1 ^ " don't match with " ^ sgoal2) 
                       
         | _ -> failwith("can't use Impl_Elim") 
       )
    | _ -> failwith("can't use Impl_Elim") 
  )
  | Not_Elim (sgoal1, sgoal2) ->  (
    match goal with
      ContextTprop (context, conclusion) ->
       let hyp1 = get_tprop_in_context context sgoal1
       and hyp2 = get_tprop_in_context context sgoal2 in
       (
         match hyp1, hyp2 with
           Not p, q ->
            if p = q
            then  ContextTprop ((fresh_ident (), Prop (Const false))::context, conclusion)
            else failwith(sgoal1 ^ " don't match with " ^ sgoal2) 
           
         | _ -> failwith("can't use Not_Elim") 
       )
    | _ -> failwith("can't use Not_Elim") 
  )
  | Exact sgoal -> (
    match goal with
      ContextTprop (context, head::tail) -> 
       let hyp = get_tprop_in_context context sgoal in
       if hyp = head
       then  ContextTprop(( remove_tprop_in_context context sgoal), tail)
       else failwith("don't match goal")
    | _ -> failwith("can't use Exact")
  )
  | Assume prop ->  (
    match goal with
      ContextTprop (context, conclusion) ->
       ContextTprop ((fresh_ident (), prop)::context, conclusion@[prop])
    | _ -> failwith("can't use Assume")
  )
  | _ -> failwith("it isn't hoare")
;;

let apply_tactic goal tactic =
  match goal with
    ContextHoare (_, _) -> failwith("non") (*apply_hoare_tactic goal tactic *)
  | ContextTprop (_, _) -> apply_prop_tactic goal tactic
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
let conclusion_1 = [prop];;
let goal_1 = ContextTprop ( context_1, conclusion_1 );;

print_goal goal_1;;
let goal_1_step_1 = apply_tactic goal_1 Impl_Intro;;
print_goal goal_1_step_1;;

let goal_1_step_2 = apply_tactic goal_1_step_1 And_Intro;;
print_goal goal_1_step_2;;



let rec apply_tactics goal tactics =
  match tactics with
  | [] -> goal
  | head::tail -> let new_goal = apply_tactic goal head in
                  (print_endline "\n__________________________________________________________________\n";
                   print_goal new_goal;
                   apply_tactics new_goal tail)
;;

let tactics = [
    Impl_Intro;
    And_Intro
  ]
;;

print_goal (apply_tactics goal_1 tactics);;


  let (ct, cc) : context * conclusion = g in
  match t with
  | And_Intro -> (
      match cc with 
      | Prop(And(p1, p2)) -> [(ct, Prop(p1)); (ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an And-formula."
    )
  | Or_Intro_1 -> (
      match cc with 
      | Prop(Or(p1, p2)) -> [(ct, Prop(p1))]
      | _ -> failwith "Tactic failure: Goal is not an Or-formula."
    )
  | Or_Intro_2 -> (
      match cc with 
      | Prop(Or(p1, p2)) -> [(ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an Or-formula."
    )
  | Impl_Intro -> (
      match cc with 
      | Prop(Impl(p1, p2)) -> [((fresh_ident(), p1)::ct, Prop(p2))]
      | _ -> failwith "Tactic failure: Goal is not an Impl-formula."
    )
  | Not_Intro -> (
      match cc with 
      | Prop(Not(p1)) -> [((fresh_ident(), p1)::ct, Prop(False))]
      | _ -> failwith "Tactic failure: Goal is not an Not-formula."
    )
  | And_Elim_1(h) -> (
      match (find_prop_context h ct) with 
      | And(p1, p2) -> [((fresh_ident(), p1)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an And-formula."
    )
  | And_Elim_2(h) -> (
      match (find_prop_context h ct) with 
      | And(p1, p2) -> [((fresh_ident(), p2)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an And-formula."
    )
  | Or_Elim(h) -> (
      match (find_prop_context h ct) with 
      | Or(p1, p2) -> [((fresh_ident(), p1)::ct, cc); ((fresh_ident(), p2)::ct, cc)]
      | _ -> failwith "Tactic failure: Hypothesis is not an Or-formula."
    )
  | Impl_Elim(h1, h2) -> (
      match (find_prop_context h1 ct) with 
      | Impl(h1_1, h1_2) -> 
          if h1_1 = (find_prop_context h2 ct) 
          then [((fresh_ident(), h1_2)::ct, cc)]
          else failwith "Tactic failure: Second hypothesis does not match the assumption of the first hypothesis."
      | _ -> failwith "Tactic failure: Hypothesis is not an Impl-formula."
    )
  | Not_Elim(h1, h2) -> (
      match (find_prop_context h1 ct) with 
      | Not(h1_1) -> 
          if h1_1 = (find_prop_context h2 ct) 
          then [((fresh_ident(), False)::ct, cc)]
          else failwith "Tactic failure: Second hypothesis does not match the body of the first hypothesis."
      | _ -> failwith "Tactic failure: Hypothesis is not an Not-formula."
    )
  | Exact(h) -> (
      match cc with
      | Prop(p) -> 
          if (find_prop_context h ct) = p
          then [] (*WIN*)
          else failwith "Tactic failure: Props are not the same."
      | _ -> failwith "Tactic failure: The conclusion is not a logical proposition."
    
    )
  | Assume(p) -> (
      [((fresh_ident(), p)::ct, cc); (ct, Prop(p))]
    )