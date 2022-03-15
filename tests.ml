#load "str.cma";;
#use "bxpr.ml";;
#use "projet.ml"

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


