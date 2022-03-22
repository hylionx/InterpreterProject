#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;
#use "hoare_triple.ml";;

(* Question 1 : *)

type goal =
  ContextHoare of (string*tprop)list * hoare_triple
|ContextTprop of (string*tprop)list *  tprop
;;


(* Question 2 : *)

let p = Prop(Const true);;
let q = Prop(Const false);;
let r = Prop(Const true);;
let impl = Implied ((Or (p, q)), r);;

let context1 = [("H", impl) ; ("H2", p)];;
let conclusion1 = Or (p, q);;
let goal1 = ContextTprop ( context1, conclusion1 );;


let goal2 = ContextHoare ( [],
                           Hoare (Equal (Var "x", Const (-3)),
                                  Cond(
                                      InfEqual(Var "x", Const 0),
                                      Affect("x", Minus(Const 0, Var "x")),
                                      Skip),
                                  Equal(Const 3, Var "x")              
                             )
              )
;;


(* Question 3 : *)

let rec context_to_string context =
    match context with
    | [] -> ""
    | (id, prop)::rl -> id ^ " : " ^ (prop_to_string prop) ^ "\n" ^ (print_context rl)
;;

print_string (context_to_string context1);;

let rec print_goal goal =
  match goal with
  | ContextHoare (context, conclusion) ->
     print_endline ( (context_to_string context1) ^ "======================\n" ^ ("prop_to_string conclusion"))
  | ContextTprop (context, conclusion) ->
     print_endline ( (context_to_string context1) ^ "======================\n" ^ (prop_to_string conclusion))      
;;

print_goal goal1;;
print_goal goal2;;


let fresh_ident =
  let prefix = " H " and count = ref 0 in
  function () -> ( count := ! count + 1 ;
                   prefix ^ ( string_of_int (! count )))
;;
