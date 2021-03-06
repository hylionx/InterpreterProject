#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml";;
#use "hoare_triple.ml";;

(* Question 1 : *)
(* Definit un type goal qui represente un but de preuve
caracterise par un context et une conclusion *)
type context = (string*tprop)list;;
type conclusion = PropConclusion of tprop | HoareConclusion of hoare_triple;;

type goal = context * conclusion;;


(* Question 2 : *)

let p = Prop(Const true);;
let q = Prop(Const false);;
let r = Prop(Const true);;
let impl = Implied ((Or (p, q)), r);;

let context1 = [("H", impl) ; ("H1", p)];;
let conclusion1 = PropConclusion (Or (p, q));;
let goal1 : goal = ( context1, conclusion1 );;

let goal2 : goal = ( [],
                     HoareConclusion
                       (Hoare (Equal (Var "x", Const (-3)),
                               Cond(
                                   InfEqual(Var "x", Const 0),
                                   Affect("x", Minus(Const 0, Var "x")),
                                   Skip),
                               Equal( Var "x", Const 3)              
                          )
                       )
                   )
;;


(* Question 3 : *)

let rec context_to_string context =
  match context with
  | [] -> ""
  | (id, prop)::rl -> id ^ " : " ^ (prop_to_string prop) ^ "\n" ^ (context_to_string rl)
;;

let rec conclusion_to_string conclusion =
  match conclusion with
  | PropConclusion (prop) -> prop_to_string prop
  | HoareConclusion (hoare) -> hoare_triple_to_string hoare
;;


print_string (context_to_string context1);;

let print_goal goal =
  match goal with
  | (context, conclusion) -> 
     let contextStr = context_to_string context 
     and conclusionStr = conclusion_to_string conclusion
     in print_endline ( 
            contextStr
            ^ "\n======================\n"
            ^ conclusionStr
          )     
;;

print_goal goal1;;
print_goal goal2;;

let count = ref 0;;
let fresh_ident =
  let prefix = "H" in
  function () -> ( count := ! count + 1 ;
                   prefix ^ ( string_of_int (! count )))
 
;;

let reset = function () ->  count := 0;;


(* Question 4

{(x = y + i - 1)/\ (i <= 10)} c {[i + 1/i](x = y + i - 1)}
------------------------------------------------------------------------repeat(i)
{[1/i](x = y + i - 1)} repeat 10 do c {(x = y + i - 1)/\ (i = 10 + 1)}

*)

(* Question 5

{(r = 0) /\ (n = 1)} repeat 5 do r := r + n; n := n + 1 od {(r = 15) /\ (n = 6)}


I = (r = i * (i-1) / 2) /\ (n = i)

{(r = 0)/\ (n = 1)}
{I}
repeat 5 do 
   {(r = i * (i-1) / 2) /\ (n = i) /\ i <= 5}
   r := r + n; 
   {(r + n = i * (i-1) / 2) /\ (n = i) /\ i <= 5}
   n := n + 1 
   {(r + n + 1 = i * (i-1) / 2) /\ (n + 1 = i) /\ i <= 5}
od
{(r = i * (i-1) / 2) /\ (n = i) /\ i = 5 + 1}
{(r = 15) /\ (n = 6)}

*)
