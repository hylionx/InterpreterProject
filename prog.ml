#use "bxpr.ml";;

(* 1.3.1 Syntaxe abstraite  *) 

(* Question 1 *)
type prog = 
  Repeat of aexpr * prog * prog
  | Skip 
  | Affect of string * aexpr * prog
  | Cond of bexpr * prog * prog * prog
  | Seq of prog * prog

;;

(* Question 2 *)

(* y := 7 *)
let prog1 = Seq(Affect("y", Const 7, Skip), Skip);;

(* z := 3 + 4 ; x := 2* x *)
let prog2 = Seq(Affect("z", Add(Const 3, Const 4),Skip), Affect("x", Mult(Const 2, Var "x"),Skip))
;;

(* n := 3; if (n <= 4) then n:= 2*n+3 else n:= n+1 *)
let prog3 = Affect("n", Const 3,
            (Cond(
                InfEqual(Var "n", Const 4),
                Seq(Affect("n", Add(Mult(Const 2, Var "n"), Const 3), Skip),Skip),
                Seq(Affect("n", Add(Var "n", Const 1), Skip),Skip),
            Skip)));;


(* repeat 10 do x := x+1 od *)
let prog4 = Repeat(Const 10,
                   Seq(Affect("x", Add(Var "x", Const 1), Skip), Skip),
                   Skip)
;;





(* Question 3 *)
let rec make_tabs number =
  if number = 0
  then ""
  else"\t" ^ make_tabs (number - 1)
;;

let rec prog_to_string_aux prog tabs =
  match prog with
   |Repeat (x,y,suite) ->
     make_tabs tabs ^ "repeat "^ aexp_to_string x ^" do\n"
     ^ prog_to_string_aux y (tabs + 1) ^ "od"
     ^ prog_to_string_aux suite tabs
   |Skip -> ""
   |Affect(x,y,Skip) ->
     make_tabs tabs ^ x^" := "^ aexp_to_string y ^ "\n"
   |Affect(x,y,suite) ->
     make_tabs tabs ^ x^" := "^ aexp_to_string y ^ " ;\n"
     ^ prog_to_string_aux suite tabs
   |Cond(x,y,Skip,suite) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n "
     ^ prog_to_string_aux suite tabs ^""
   |Cond(x,y,z,suite) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n"
     ^ make_tabs tabs ^"else {\n"
     ^ prog_to_string_aux z (tabs + 1)
     ^ make_tabs tabs ^"}\n "
     ^ prog_to_string_aux suite tabs
   |Seq(x,y) ->
     make_tabs tabs ^"("^ prog_to_string_aux x tabs ^ "); "^ prog_to_string_aux y tabs
        
     
;;

let prog_to_string prog =
  prog_to_string_aux prog 0
;;

print_string (prog_to_string prog1);;
print_string (prog_to_string prog2);;
print_string (prog_to_string prog3);;
print_string (prog_to_string prog4);;

(*******Interpretation ******)
(* Question 4 *)
let rec selfcompose func n =
  match n with
  | 0 -> fun v -> v
  | _ -> fun v -> func (selfcompose (func) (n-1) v) 
;;

(* Question 5 *)
let plus2 x =  x + 2;;

let f = selfcompose plus2 10 ;;
let calcul1 = f 0;;



(* Question 6 *)
let rec putValuation var exp valuation =
  match valuation with
    [] -> [(var, ainterp exp valuation)]
  | ((v, e)::tail) -> if v = var
                      then (var, ainterp exp valuation)::tail
                      else (v, e):: (putValuation var exp tail)
;;


let rec exec programme valuation =
  match programme with
    Repeat(exp, content, next) ->
     let rep = ainterp exp valuation in
     let myfunc = (selfcompose (exec content)  rep) in
    exec next (myfunc valuation)  
  | Skip -> valuation    
  | Seq (c1,c2) -> exec c2 (exec c1 valuation)
  | Affect (var, axp, next) -> exec next (putValuation var axp valuation)
  | Cond (bxp, t, e, next) -> 
     match binterp bxp valuation with
       true -> exec next (exec t valuation)
     | false -> exec next (exec e valuation)
  
           
;;

exec prog1 [];;
exec prog2 [];;
exec prog3 [];;
exec prog4 [];;

(* Question 7 *)
let rec fact value =
  if value < 0
  then failwith("Can't calculate with negetive value")
  else 
    match value with
      0 -> 1
    | _ -> value * (fact (value - 1))
;;

fact 5;;

