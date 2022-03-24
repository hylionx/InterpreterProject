#use "bxpr.ml";;

(* 1.3.1 Syntaxe abstraite  *) 

(* Question 1 *)
type prog = 
  Repeat of aexpr * prog 
  | Skip 
  | Affect of string * aexpr
  | Cond of bexpr * prog * prog
  | Seq of prog * prog
;;

(* Question 2 *)

(* y := 7 *)
let prog1 = Seq(Affect("y", Const 7), Skip);;

(* z := 3 + 4 ; x := 2* x *)
let prog2 = Seq(Affect("z", Add(Const 3, Const 4)),Seq(Affect("x", Mult(Const 2, Var "x")), Skip));;

(* n := 3; if (n <= 4) then n:= 2*n+3 else n:= n+1 *)
let prog3 = Seq(Affect("n", Const 3),
            Seq(Cond(
                    InfEqual(Var "n", Const 4),
                    Seq(Affect("n", Add(Mult(Const 2, Var "n"), Const 3)),
                        Skip),
                    Seq(Affect("n", Add(Var "n", Const 1)),
                        Skip)),
                Skip));;


(* repeat 10 do x := x+1 od *)
let prog4 = Seq(Repeat(Const 10,
                       Seq(Affect("x", Add(Var "x", Const 1)),
                           Skip)),
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
   |Repeat (x,y) ->
     make_tabs tabs ^ "repeat "^ aexp_to_string x ^" do\n"
     ^ prog_to_string_aux y (tabs + 1) ^ "\n"
     ^ make_tabs tabs ^ "od"
   |Skip -> ""
   |Affect(x,y) ->
     make_tabs tabs ^ x^" := "^ aexp_to_string y
   |Cond(x,y,Skip) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n "
   |Cond(x,y,z) ->
     make_tabs tabs ^ "if ("^bexp_to_string x ^ ")\n"
     ^ make_tabs tabs ^"then {\n"
     ^ prog_to_string_aux y (tabs + 1)
     ^ make_tabs tabs ^"}\n"
     ^ make_tabs tabs ^"else {\n"
     ^ prog_to_string_aux z (tabs + 1) ^ "/n"
     ^ make_tabs tabs ^"} "
   |Seq(x,Skip) ->
     prog_to_string_aux x tabs
   |Seq(x,y) ->
     prog_to_string_aux x tabs ^ ";\n"^ prog_to_string_aux y tabs
        
     
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
  if n <= 0
  then  fun prog -> prog
  else  fun prog -> func (selfcompose (func) (n-1) prog) 
;;

(* Question 5 *)
let plus2 x =  x + 2;;

let f = selfcompose plus2 10 ;;
let calcul1 = f 0;;



(* Question 6 *)
let rec putValuation var value valuation =
  match valuation with
    [] -> [(var, value)]
  | ((v, e)::tail) -> if v = var
                      then ((var, value)::tail)
                      else (v, e):: (putValuation var value tail)
;;


let rec valuation_to_string valuation =
  match valuation with
    [] -> ""
  | ((v, e)::tail) -> "(" ^ v ^" , " ^ string_of_int e ^ ") ;  " ^ valuation_to_string tail
;;

 let rec exec programme valuation =
  match programme with
    Repeat(exp, content) ->
     let rep = ainterp exp valuation in
     let myfunc = (selfcompose (exec content)  rep) in
    myfunc valuation 
  | Skip -> valuation    
  | Seq (c1,c2) ->
     let new_val = (exec c1 valuation) in
     exec c2 new_val
  | Affect (var, axp) ->
     let value = (ainterp axp valuation)  in
     putValuation var value valuation
  | Cond (bxp, t, e) -> 
     match binterp bxp valuation with
       true -> exec t valuation
     | false -> exec e valuation
  
           
;;

exec prog1 [];;
exec prog2 [];;
exec prog3 [];;
exec prog4 [];;

(* Question 7 *)
let init_fact v next= Seq(Affect("i", Const v),
                          Seq(Affect("res", Const 1),
                              Seq(next,
                                  Skip)
                            )
                        );;

let prog_fact v =  init_fact v (Repeat(Const v,
                                       Seq(Affect("res", Mult(Var "res", Var "i")),
                                             Seq(Affect("i", Minus(Var "i", Const 1)),
                                                 Skip)))              
                                   );;
                            

let fact v = prog_fact v;;      
exec (fact 5) [];;

let fibonacci n = Seq(Affect("n", Const n),
                      Seq(Affect("a", Const 0),
                          Seq(Affect("b", Const 1),
                              Seq(Repeat(
                                      Minus(Var "n", Const 1),
                                      Seq(Affect("c", Add(Var"a", Var "b")),
                                          Seq(Affect("a", Var "b"),
                                              Seq(Affect("b", Var "c"),
                                                  Skip
                                                )
                                    ))),
                                    Skip
                            ))))
;;

   
exec (fibonacci 5) [];;
exec (fibonacci 6) [];;
exec (fibonacci 7) [];;
exec (fibonacci 8) [];;
exec (fibonacci 9) [];;
exec (fibonacci 10) [];;
