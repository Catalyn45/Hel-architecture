(* Proiect coq *)

Require Import Strings.String.
Local Open Scope string_scope.
Require Import Lists.List.
Local Open Scope list_scope.

(* Tipuri *)

Inductive Var :=
| from_string : string -> Var.

Inductive Nat :=
| nat_err : Nat
| nat_val : nat -> Nat.

Inductive Bool :=
| bool_err : Bool
| b_true : Bool
| b_false : Bool.

Inductive String :=
|str_err : String
|str_val : string -> String.

(* Expresii *)

Inductive Aexp :=
| a_var : Var -> Aexp
| a_nat : Nat -> Aexp
| a_bool : Bool -> Aexp
| a_add : Aexp -> Aexp -> Aexp
| a_sub : Aexp -> Aexp -> Aexp
| a_mul : Aexp -> Aexp -> Aexp
| a_div : Aexp -> Aexp -> Aexp
| a_mod : Aexp -> Aexp -> Aexp
| a_bool_to_nat : Bool -> Aexp.

Inductive Bexp :=
| b_var : Var -> Bexp
| b_bool : Bool -> Bexp
| b_not : Bexp -> Bexp
| b_and : Bexp -> Bexp -> Bexp
| b_or : Bexp -> Bexp -> Bexp
| b_equal : Aexp -> Aexp -> Bexp
| b_different : Aexp -> Aexp -> Bexp
| b_less : Aexp -> Aexp -> Bexp
| b_greater : Aexp -> Aexp -> Bexp
| b_less_equal : Aexp -> Aexp -> Bexp
| b_greater_equal : Aexp -> Aexp -> Bexp
| b_nat_to_bool : Nat -> Bexp.

Inductive STRexp :=
| s_var : Var -> STRexp
| s_str : String -> STRexp
| s_concat: STRexp -> STRexp -> STRexp.

Inductive Exp :=
| e_Aexp : Aexp -> Exp
| e_Bexp : Bexp -> Exp
| e_STRexp : STRexp -> Exp.

Inductive Adress :=
| ad_var : Var -> Adress.

Inductive Declaration :=
| decl_nat_exp : Var -> Aexp -> Declaration
| decl_bool_exp : Var -> Bexp -> Declaration
| decl_string_exp : Var -> STRexp -> Declaration
| decl_nat : Var -> Declaration
| decl_bool : Var -> Declaration
| decl_string : Var -> Declaration
| decl_struct: Var -> list Declaration -> Declaration
| decl_vect_nat : Var -> nat -> Declaration
| decl_vect_bool : Var -> nat -> Declaration
| decl_vect_string : Var -> nat -> Declaration
| decl_vect_nat_init : Var -> nat -> list Nat -> Declaration
| decl_vect_bool_init : Var -> nat -> list Bool -> Declaration
| decl_vect_string_init : Var -> nat -> list String -> Declaration
| decl_pointer_nat : Var -> Declaration
| decl_pointer_bool : Var -> Declaration
| decl_pointer_string : Var -> Declaration
| decl_pointer_nat_init : Var -> Adress -> Declaration
| decl_pointer_bool_init : Var -> Adress -> Declaration
| decl_pointer_string_init : Var -> Adress -> Declaration.


Inductive Stmt :=
| assignment : Var -> Aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| decl: Declaration -> Stmt
| while : Bexp -> Stmt -> Stmt
| for_stmt : Stmt -> Bexp -> Stmt -> Stmt ->Stmt
| if_then : Bexp -> Stmt -> Stmt
| if_then_else : Bexp -> Stmt -> Stmt -> Stmt
| call_fun : Var -> list Exp -> Stmt.

Inductive Global :=
| decl_fun_nat: Var -> list Declaration -> Stmt -> Global
| decl_fun_bool: Var -> list Declaration -> Stmt -> Global
| decl_fun_string: Var -> list Declaration -> Stmt -> Global.

(* Corections *)

Coercion nat_val : nat >-> Nat.
Coercion a_nat : Nat >-> Aexp.
Coercion e_Aexp : Aexp >-> Exp.

Coercion b_bool : Bool >-> Bexp.
Coercion e_Bexp : Bexp >-> Exp.

Coercion str_val : string >-> String.
Coercion s_str : String >-> STRexp.

Coercion decl : Declaration >-> Stmt.

Coercion a_var : Var >-> Aexp.

Coercion from_string : string >-> Var.


(* Notatii *)

Notation "A1 +' A2" := (a_add A1 A2) (at level 48).
Notation "A1 -' A2" := (a_sub A1 A2) (at level 48).
Notation "A1 *' A2" := (a_mul A1 A2) (at level 46).
Notation "A1 /' A2" := (a_div A1 A2) (at level 46).
Notation "A1 %' A2" := (a_mod A1 A2) (at level 46).

Notation "A1 <' A2" := (b_less A1 A2) (at level 53).
Notation "A1 >' A2" := (b_greater A1 A2) (at level 53).
Notation "A1 <=' A2" := (b_less_equal A1 A2) (at level 53).
Notation "A1 >=' A2" := (b_greater_equal A1 A2) (at level 53).
Notation "A1 ==' A2" := (b_equal A1 A2) (at level 53).
Notation "A1 !=' A2" := (b_different A1 A2) (at level 53).
Notation "B1 ||' B2" := (b_or B1 B2) (at level 55).
Notation " '!'' B " := (b_not B) (at level 40).
Notation "B1 &&' B2" := (b_and B1 B2) (at level 55).

Notation "STR1 <--> STR2" := (s_concat STR1 STR2) (at level 53).

Notation "'uint'' A |" := (decl_nat A)(at level 50).
Notation "'uint'' A --> V" := (decl_nat_exp A  V)(at level 50).

Notation "'uint'*' A |" := (decl_pointer_nat A)(at level 50).
Notation "'uint'*' A --> AD" := (decl_pointer_nat_init A AD) (at level 50).

Notation "'bool'' B |" := (decl_bool B)(at level 50).
Notation "'bool'' B --> V" := (decl_bool_exp B  V)(at level 50).

Notation "'bool'*' B --> AD" := (decl_pointer_nat_init B AD) (at level 50).
Notation "'bool'*' B |" := (decl_pointer_bool B)(at level 50).

Notation "'string'' S |" := (decl_string S)(at level 50).
Notation "'string'' S --> V" := (decl_string_exp S  V)(at level 50).

Notation "'string'*' S --> AD" := (decl_pointer_nat_init S AD) (at level 50).
Notation "'string'*' S |" := (decl_pointer_bool S)(at level 50).

Notation "'struct'' A '{'' D1 ; D2 ; .. ; Dn '}''" := (decl_struct A (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).

Notation "&' V" := (ad_var V) (at level 50).

Notation "S1 ;; S2" := (sequence S1 S2) (at level 92).

Notation "V ::= A" := (assignment V A) (at level 50).

Notation "'if'' ( B ) { S }" := (if_then B S) (at level 50).

Notation "'if_else'' ( B ) { S1 } 'else'' { S2 }" := (if_then_else B S1 S2) (at level 50).

Notation "'while' ( B ) { S }" := (while B S) (at level 50).

Notation "'for'' ( S1 ; B ; S2 ) { S3 }" := (for_stmt S1 B S2 S3) (at level 50).

Notation "'uint'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_nat N (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S) (at level 50).
Notation "'bool'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_bool N (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S) (at level 50).
Notation "'string'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_string N (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S) (at level 50).

Notation "'uint'' V [ Sz ]" := ( decl_vect_nat V Sz) (at level 50). 
Notation "'bool'' V [ Sz ]" := ( decl_vect_bool V Sz) (at level 50). 
Notation "'string'' V [ Sz ]" := ( decl_vect_string V Sz) (at level 50). 

Notation "(uint) B" := ( a_bool_to_nat B ) ( at level 50 ).
Notation "(bool) A" := ( b_nat_to_bool A ) ( at level 50 ).

Notation "'uint'' V [ Sz ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_nat_init V Sz (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).

Notation "N ''(' P1 , P2 , .. , Pn '')'" := (call_fun N (cons P1 ( cons P2 .. (cons Pn nil) .. ) )) (at level 50).

(* Compute *)

Compute (bool) 10.

Compute (uint) b_true.

Compute if_else' (b_true) { bool' "a" | } else' { bool' "b" |}.

Compute uint' "a" --> 10.
Compute uint' "b" |.

Compute bool' "a" |.
Compute bool' "b" --> b_true.

Compute string' "a" |.
Compute string' "a" --> "Buna ziua!".

Compute while (b_true) { bool' "a" | }.

Compute uint' "vect" [ 50 ].

Compute uint' "vect" [ 50 ] --> {' nat_val 10 , nat_val 20 }'.

Compute uint' "function_name" (' uint' "a" | , uint' "b" | )' {' "c" ::= 10}'.

Compute "function_name" '( e_Bexp b_false , e_Aexp 10 , e_Bexp b_false ') .

Compute for' (uint' "i" --> 0 ; "i" <' 10 ; "i" ::= "i" +' 1 ) { "suma" ::= "suma" +' "i" }.

Compute string' "a" | ;; string' "b" |.

Compute struct' "my_struct" {' uint' "a" | ; uint' "b" |}'.

Compute uint'* "pointer" |.

Compute uint'* "pointer" --> &'"x".
