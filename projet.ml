#load "str.cma";;
#use "bxpr.ml";;

(*
garbage 


let replace var replace_by input = Str.global_replace (Str.regexp_string var) replace_by input;;

replace "x" "5" (aexp_to_string (expr9));;

let rec replace_all my_valuation expr =
  match my_valuation with
  | [] -> expr
  | (var , replace_by) :: rl -> replace_all rl (replace var (string_of_int replace_by) expr)
;;

replace_all  my_valuation (aexp_to_string (expr9));;
 *)

(* 1.3.1 Syntaxe abstraite  *) 

(* Question 1 *)
type prog = 
  Repeat of aexpr * prog * prog 
  | Skip 
  | Affect of string * aexpr * prog
  | Cond of bexpr * prog * prog * prog
;;

(* Question 2 *)

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
  | _ -> fun v -> func (selfcompose func (n-1) v) 
;;

(* Question 5 *)
let plus2 x =  x + 2;;

let f = selfcompose plus2 10 ;;
let calcul1 = f 0;;

(* Question 6 *)
let rec exec programme valuation =
  match programme with
  Repeat(exp, contenu, suite) -> exec suite (selfcompose exec (ainterp contenu valuation))  
  | Skip -> valuation
  | Affect of string * aexpr * prog
  | Cond of bexpr * prog * prog * prog
;;
