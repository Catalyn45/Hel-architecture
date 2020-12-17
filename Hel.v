(* Proiect coq *)

Require Import Strings.String.
Local Open Scope string_scope.

(* Tipuri *)

Inductive Nat :=
| nat_err : Nat
| nat_val : nat -> Nat.

Inductive Bool :=
| bool_err : Bool
| bool_val : bool -> Bool.

Inductive String :=
|str_err : String
|str_val : string -> String.


(* Expresii *)

Inductive Aexp :=
| a_nat : Nat -> Aexp
| a_bool : Bool -> Aexp
| a_add : Aexp -> Aexp -> Aexp
| a_sub : Aexp -> Aexp -> Aexp
| a_mul : Aexp -> Aexp -> Aexp
| a_div : Aexp -> Aexp -> Aexp.

Inductive Bexp :=
| b_true : Bool -> Bexp
| b_false : Bool -> Bexp
| b_not : Bexp -> Bexp
| b_and : Bexp -> Bexp -> Bexp
| b_or : Bexp -> Bexp -> Bexp
| b_equal : Bexp -> Bexp -> Bexp.

Inductive STRexp :=
| s_str : String -> STRexp
| s_concat: STRexp -> STRexp -> STRexp.