(* Proiect coq *)

(* Sintaxa *)

Require Import Strings.String.
Local Open Scope string_scope.
Require Import Lists.List.
Local Open Scope list_scope.

(* Tipuri *)

Inductive Natural :=
| nat_err : Natural
| nat_val : nat -> Natural.

Inductive Bool :=
| bool_err : Bool
| b_true : Bool
| b_false : Bool.

Inductive String :=
|str_err : String
|str_val : string -> String.

Inductive Address :=
| ad_var : string -> Address
| ad_err : Address.

Inductive Vector :=
| vect_err : Vector
| vect_nat : list Natural -> Vector
| vect_bool : list Bool -> Vector
| vect_str : list String -> Vector.

(* Expresii *)

Inductive Aexp :=
| a_var : string -> Aexp
| a_nat : Natural -> Aexp
| a_add : Aexp -> Aexp -> Aexp
| a_sub : Aexp -> Aexp -> Aexp
| a_mul : Aexp -> Aexp -> Aexp
| a_div : Aexp -> Aexp -> Aexp
| a_mod : Aexp -> Aexp -> Aexp
| a_bool_to_nat : Bool -> Aexp
| a_get_vect_val : string -> nat -> Aexp.

Inductive Bexp :=
| b_var : string -> Bexp
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
| b_nat_to_bool : Natural -> Bexp
| b_get_vect_val : string -> nat -> Bexp.

Inductive STRexp :=
| s_var : string -> STRexp
| s_str : String -> STRexp
| s_concat: STRexp -> STRexp -> STRexp
| s_get_vect_val : string -> nat -> STRexp.

Inductive Declaration :=
| decl_nat_exp : string -> Aexp -> Declaration
| decl_bool_exp : string -> Bexp -> Declaration
| decl_string_exp : string -> STRexp -> Declaration
| decl_nat : string -> Declaration
| decl_bool : string -> Declaration
| decl_string : string -> Declaration
| decl_struct: string -> list Declaration -> Declaration
| decl_vect_nat : string -> nat -> Declaration
| decl_vect_bool : string -> nat -> Declaration
| decl_vect_string : string -> nat -> Declaration
| decl_vect_nat_init : string -> nat -> list Natural -> Declaration
| decl_vect_bool_init : string -> nat -> list Bool -> Declaration
| decl_vect_string_init : string -> nat -> list String -> Declaration
| decl_pointer_nat : string -> Declaration
| decl_pointer_bool : string -> Declaration
| decl_pointer_string : string -> Declaration
| decl_pointer_nat_init : string -> Address -> Declaration
| decl_pointer_bool_init : string -> Address -> Declaration
| decl_pointer_string_init : string -> Address -> Declaration.

Inductive param_vals :=
| param_nat : Natural -> param_vals
| param_bool : Bool -> param_vals
| param_string : String -> param_vals.

Inductive Stmt :=
| stm_err : Stmt
| assignment : string -> Aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| decl: Declaration -> Stmt
| while : Bexp -> Stmt -> Stmt
| for_stmt : Stmt -> Bexp -> Stmt -> Stmt ->Stmt
| if_then : Bexp -> Stmt -> Stmt
| if_then_else : Bexp -> Stmt -> Stmt -> Stmt
| call_fun : string -> list param_vals -> Stmt
| get_vect_elem : string -> nat -> Stmt.

Inductive value :=
| undecl : value
| uninitialized: value
| value_nat : Natural -> value
| value_bool : Bool -> value
| value_string : String -> value
| value_address : Address -> value
| value_parameters : list Declaration -> Stmt -> value
| value_vector : Vector -> value.

Inductive Global :=
| decl_fun_nat: string -> value -> Global
| decl_fun_bool: string -> value -> Global
| decl_fun_string: string -> value -> Global
| decl_fun_main : Stmt -> Global.

(* Corections *)

Coercion nat_val : nat >-> Natural.
Coercion a_nat : Natural >-> Aexp.

Coercion b_bool : Bool >-> Bexp.

Coercion str_val : string >-> String.
Coercion s_str : String >-> STRexp.

Coercion decl : Declaration >-> Stmt.

Coercion a_var : string >-> Aexp.


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

Notation "'struct'' S '{'' D1 ; D2 ; .. ; Dn '}''" := (decl_struct S (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).

Notation "&' V" := (ad_var V) (at level 50).

Notation "S1 ;; S2" := (sequence S1 S2) (at level 92).

Notation "V ::= A" := (assignment V A) (at level 50).

Notation "'if'' ( B ) { S }" := (if_then B S) (at level 50).

Notation "'if_else'' ( B ) { S1 } 'else'' { S2 }" := (if_then_else B S1 S2) (at level 50).

Notation "'while' ( B ) { S }" := (while B S) (at level 50).

Notation "'for'' ( S1 ; B ; S2 ) { S3 }" := (for_stmt S1 B S2 S3) (at level 50).

Notation "'uint'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_nat N (value_parameters (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S)) (at level 50).
Notation "'bool'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_bool N (value_parameters (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S)) (at level 50).
Notation "'string'' N '('' D1 , D2 , .. , Dn ')'' '{'' S '}''" := (decl_fun_string N (value_parameters (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) S)) (at level 50).
Notation "'main(){'' S '}''" := (decl_fun_main S) (at level 50).

Notation "'uint'' V [ Sz ]" := ( decl_vect_nat V Sz) (at level 50). 
Notation "'bool'' V [ Sz ]" := ( decl_vect_bool V Sz) (at level 50). 
Notation "'string'' V [ Sz ]" := ( decl_vect_string V Sz) (at level 50). 

Notation "(uint) B" := ( a_bool_to_nat B ) ( at level 50 ).
Notation "(bool) A" := ( b_nat_to_bool A ) ( at level 50 ).

Notation "'uint'' V [ Sz ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_nat_init V Sz (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'bool'' V [ Sz ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_bool_init V Sz (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string'' V [ Sz ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_string_init V Sz (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).

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

Compute "function_name" '( param_bool b_false , param_nat 10 , param_bool b_false ') .

Compute for' (uint' "i" --> 0 ; "i" <' 10 ; "i" ::= "i" +' 1 ) { "suma" ::= "suma" +' "i" }.

Compute string' "a" | ;; string' "b" |.

Compute struct' "my_struct" {' uint' "a" | ; uint' "b" |}'.

Compute uint'* "pointer" |.

Compute uint'* "pointer" --> &'"x".

(* Semantica *)

Definition get_nat (v : value) : Natural :=
match v with
| value_nat n => n
| _ => nat_err
end.

Definition get_bool (v : value) : Bool :=
match v with
| value_bool b => b 
| _ => bool_err
end.

Definition get_str (v : value) : String :=
match v with
| value_string s => s
| _ => str_err
end.

Definition get_addr (v : value) : Address :=
match v with
| value_address a => a
| _ => ad_err
end.

Coercion value_nat: Natural >-> value.
Coercion value_bool: Bool >-> value.
Coercion value_string : String >-> value.
Coercion value_vector : Vector >-> value.
Coercion value_address : Address >-> value.

Definition Env := string -> value.

Definition update_value (env : Env)
           (x : string) (v : value) : Env :=
  fun y =>
    if (string_dec y x)
    then v
    else (env y).

Definition update (env : Env)
           (x : string) : Env := (update_value env x uninitialized).

Definition env0 := fun( var : string ) => undecl.
Check env0.

Definition env1 := (update_value env0 "n" "bbbbb").
Definition env2 := (update env1 "s").

Compute env1 "n".

Definition add_nat (a1 a2 : Natural) : Natural :=
match a1, a2 with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val n1, nat_val n2 => nat_val (n1 + n2)
end.

Definition mul_nat (a1 a2 : Natural) : Natural :=
match a1, a2 with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val n1, nat_val n2 => n1 * n2
end.

Definition sub_nat (a1 a2 : Natural) : Natural :=
match a1, a2 with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val n1, nat_val n2 => n1 - n2
end.

Definition div_nat (a1 a2 : Natural) : Natural :=
match a1, a2 with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val n1, nat_val n2 => Nat.div n1 n2
end.

Definition mod_nat (a1 a2 : Natural) : Natural :=
match a1, a2 with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val n1, nat_val n2 => Nat.modulo n1 n2
end.

Definition conv_bool_nat ( b : Bool) : Natural :=
match b with
| b_true => 1
| _ => 0
end.

Fixpoint get_from_nat_vector (l : list Natural) (n : nat) : Natural :=
match n, l with
| O, x::l1 => x
| S m, nil => nat_err
| S m, x::l2 => (get_from_nat_vector l2 m)
| _, _ => nat_err
end.

Fixpoint get_from_bool_vector (l : list Bool) (n : nat) : Bool :=
match n, l with
| O, x::l1 => x
| S m, nil => bool_err
| S m, x::l2 => (get_from_bool_vector l2 m)
| _, _ => bool_err
end.

Fixpoint get_from_str_vector (l : list String) (n : nat) : String :=
match n, l with
| O, x::l1 => x
| S m, nil => str_err
| S m, x::l2 => (get_from_str_vector l2 m)
| _, _ => str_err
end.

Definition get_element ( v : value) (n : nat ) : value :=
match v, n with
| undecl, _ => nat_err
| value_vector vec, n1 => 
                          match vec, n1 with 
                            | vect_nat vn, n2 => get_from_nat_vector vn n1
                            | vect_bool vb, n2 => get_from_bool_vector vb n2
                            | vect_str vs, n2 => get_from_str_vector vs n2
                            | _, _ => nat_err
                          end
| _, _ => nat_err
end.

Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : Aexp -> Env -> Natural -> Prop :=
| e_aconst : forall n sigma, a_nat n =[ sigma ]=> n 
| e_avar : forall v sigma, a_var v =[ sigma ]=> (get_nat (sigma v))
| e_add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  add_nat i1 i2 ->
    a1 +' a2 =[sigma]=> n
| e_mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mul_nat i1 i2 ->
    a1 *' a2 =[sigma]=> n
| e_sub : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  sub_nat i1 i2 ->
    a1 -' a2 =[sigma]=> n
| e_div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  div_nat i1 i2 ->
    a1 /' a2 =[sigma]=> n
| e_mod : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  mod_nat i1 i2 ->
    a1 %' a2 =[sigma]=> n
| e_bool_to_nat : forall b sigma, a_bool_to_nat b =[ sigma ]=> conv_bool_nat b

| e_aget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  a_get_vect_val v1 n =[ sigma ]=> get_nat (get_element v2 n)

where "a =[ sigma ]=> n" := (aeval a sigma n).

Definition b_to_Bool(b : bool) : Bool :=
match b with
| true => b_true
| false => b_false
end.

Definition less_than(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (Nat.ltb n1 n2)
end.

Definition less_equal_than(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (Nat.leb n1 n2)
end.

Definition greater_than(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (Nat.leb n2 n1)
end.

Definition greater_equal_than(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (Nat.ltb n2 n1)
end.

Definition equality(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (Nat.eqb n1 n2)
end.

Definition different(a1 a2 : Natural) : Bool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => b_to_Bool (negb (Nat.eqb n1 n2))
end.


Definition conv_nat_bool(n : Natural) : Bool :=
match n with
| nat_val 0 => b_false
| nat_err => bool_err
| _ => b_true
end.


Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : Bexp -> Env -> Bool -> Prop :=
| e_true : forall sigma, b_true ={ sigma }=> b_true
| e_false : forall sigma, b_false ={ sigma }=> b_false

| e_b_var : forall v sigma, b_var v ={ sigma }=> get_bool (sigma v)

| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_than (get_nat i1) (get_nat i2) ->
    a1 <' a2 ={ sigma }=> b

| e_less_equal_than : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_equal_than (get_nat i1) (get_nat i2) ->
    a1 <=' a2 ={ sigma }=> b

| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = greater_than (get_nat i1) (get_nat i2) ->
    a1 <' a2 ={ sigma }=> b

| e_grater_equal_than : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_equal_than i1 i2->
    a1 <=' a2 ={ sigma }=> b

| e_nottrue : forall b sigma,
    b ={ sigma }=> b_true ->
    !'b ={ sigma }=> b_false

| e_notfalse : forall b sigma,
    b ={ sigma }=> b_false ->
    !'b ={ sigma }=> b_true

| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> b_true ->
    b2 ={ sigma }=> t ->
    b1 &&' b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> b_false ->
    b1 &&' b2 ={ sigma }=> b_false

| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> b_true ->
    b1 ||' b2 ={ sigma }=> b_true

| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> b_false ->
    b2 ={ sigma }=> t ->
    b1 ||' b2 ={ sigma }=> t

| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = equality i1 i2 ->
    a1 ==' a2 ={ sigma }=> b

| e_different : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = different i1 i2 ->
    a1 ==' a2 ={ sigma }=> b

| e_nat_to_bool : forall a sigma,  b_nat_to_bool a ={ sigma }=> conv_nat_bool a

| e_bget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  b_get_vect_val v1 n ={ sigma }=> get_bool (get_element v2 n)

where "B ={ S }=> B'" := (beval B S B').

Definition concatenate(s1 s2 : String) : String :=
match s1, s2 with
  |_, str_err => str_err
  |str_err, _ => str_err
  |str_val s1, str_val s2 => str_val (s1 ++ s2)
end.

Reserved Notation "B  =< S >=> B'" (at level 80).
Inductive streval : STRexp -> Env -> String -> Prop :=
| e_str_var : forall v sigma, s_var v =< sigma >=> get_str (sigma v)
| e_str_const : forall v sigma, s_str v =< sigma >=> v
| e_concat : forall s1 s2 i1 i2 sigma s,
    s1 =< sigma >=> i1->
    s2 =< sigma >=> i2 ->
    s = concatenate i1 i2 ->
    s1 <--> s2 =< sigma >=> s

| e_sget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  s_get_vect_val v1 n =< sigma >=> get_str (get_element v2 n)

where "B =< S >=> B'" := (streval B S B').

Fixpoint update_vars ( sigma : Env ) (p : list Declaration) ( l : list param_vals ) : Env :=
match l with
| nil => sigma
| x::l' => match x, p with
           | param_nat n, y::l'' => match y with
                                    | decl_nat nt => update_vars (update_value sigma nt n) l'' l'
                                    | decl_bool bt => update_vars (update_value sigma bt n) l'' l'
                                    | decl_string st => update_vars (update_value sigma st n) l'' l'
                                    | _ => sigma
                                    end
           | _, _ => sigma
           end
end.


Definition call_f (sigma : Env ) ( v : string) ( p : value ) (l' : list param_vals) : Env :=
match p with
| value_parameters l st => update_vars sigma l l'
| _ => sigma
end.

Definition get_st (v : value) : Stmt :=
match v with
| value_parameters l st => st
| _ => stm_err
end.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_decl_nat : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_nat v -{ sigma }-> sigma'

| e_decl_bool : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_bool v -{ sigma }-> sigma'

| e_decl_string : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_string v -{ sigma }-> sigma'

| e_decl_nat_init : forall v x sigma sigma',
    sigma' = (update_value sigma v x) ->
    decl_nat_exp v (get_nat x) -{ sigma }-> sigma'

| e_decl_bool_init : forall v x sigma sigma',
    sigma' = (update_value sigma v x) ->
    decl_bool_exp v (get_bool x) -{ sigma }-> sigma'

| e_decl_string_init : forall v x sigma sigma',
    sigma' = (update_value sigma v x) ->
    decl_string_exp v (get_str x) -{ sigma }-> sigma'

| e_decl_pointer_nat : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_pointer_nat v -{ sigma }-> sigma'

| e_decl_pointer_bool : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_pointer_bool v -{ sigma }-> sigma'

| e_decl_pointer_str : forall v sigma sigma',
    sigma' = (update sigma v) ->
    decl_pointer_string v -{ sigma }-> sigma'

| e_decl_pointer_nat_init : forall v a sigma sigma',
    sigma' = (update_value sigma v a) ->
    decl_pointer_nat_init v (get_addr a) -{ sigma }-> sigma'

| e_decl_pointer_bool_init : forall v a sigma sigma',
    sigma' = (update_value sigma v a) ->
    decl_pointer_bool_init v (get_addr a) -{ sigma }-> sigma'

| e_decl_pointer_str_init : forall v a sigma sigma',
    sigma' = (update_value sigma v a) ->
    decl_pointer_string_init v (get_addr a) -{ sigma }-> sigma'

| e_decl_vect_nat : forall v x sigma sigma',
    sigma' = (update sigma v) ->
    decl_vect_nat v x -{ sigma }-> sigma'

| e_decl_vect_bool : forall v x sigma sigma',
    sigma' = (update sigma v) ->
    decl_vect_bool v x -{ sigma }-> sigma'

| e_decl_vect_string : forall v x sigma sigma',
    sigma' = (update sigma v) ->
    decl_vect_string v x -{ sigma }-> sigma'

| e_decl_vect_nat_init : forall v x l sigma sigma',
    sigma' = (update_value sigma v (vect_nat l)) ->
    decl_vect_nat_init v x l -{ sigma }-> sigma'

| e_decl_vect_bool_init : forall v l x sigma sigma',
    sigma' = (update_value sigma v (vect_bool l)) ->
    decl_vect_bool_init v x l -{ sigma }-> sigma'

| e_decl_vect_string_init : forall v x l sigma sigma',
    sigma' = (update_value sigma v (vect_str l)) ->
    decl_vect_string_init v x l -{ sigma }-> sigma'

| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update_value sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> b_false ->
    while ( b ) { s } -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> b_true ->
    (s ;; while ( b ) { s }) -{ sigma }-> sigma' ->
    while ( b ) { s } -{ sigma }-> sigma'
| e_ifthen_false : forall b s sigma,
    b ={ sigma }=> b_false ->
    if_then b s -{ sigma }-> sigma
| e_ifthen_true : forall b s sigma sigma',
    b ={ sigma }=> b_true ->
    s -{ sigma }-> sigma'->
    if_then b s -{ sigma }-> sigma'
| e_ifthenelse_false : forall b s1 s2 sigma sigma',
    b ={ sigma }=> b_false ->
    s2 -{ sigma }-> sigma'->
    if_then_else b s1 s2 -{ sigma }-> sigma'

| e_ifthenelse_true : forall b s1 s2 sigma sigma',
    b ={ sigma }=> b_true ->
    s1 -{ sigma }-> sigma'->
    if_then_else b s1 s2 -{ sigma }-> sigma'

| e_forfalse : forall s1 b s2 s3 sigma sigma',
    s1 -{ sigma }-> sigma' ->
    b ={ sigma' }=> b_false ->
    for' (s1 ; b ; s2) { s3 } -{ sigma }-> sigma'

| e_fortrue : forall s1 b s2 s3 sigma sigma' sigma'',
    s1 -{ sigma }-> sigma' ->
    b ={ sigma' }=> b_true ->
    (s3 ;; s2 ;; for' (s1 ; b ; s2 ) { s3 }) -{ sigma' }-> sigma'' ->
    for' (s1 ; b ; s2) { s3 } -{ sigma }-> sigma''

| e_call : forall v p sigma sigma' sigma'',
    sigma' = call_f sigma v (sigma v) p ->
    get_st (sigma v) -{ sigma' }-> sigma''->
    call_fun v p -{ sigma }-> sigma''

where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


Reserved Notation "G ->{ Sigma }-> Sigma'" (at level 60).

Inductive geval : Global -> Env -> Env -> Prop :=
| e_decl_fun_nat : forall v p sigma sigma',
  sigma' = (update_value sigma v p) ->
  decl_fun_nat v p ->{ sigma }-> sigma'

| e_decl_fun_bool : forall v p sigma sigma',
  sigma' = (update_value sigma v p) ->
  decl_fun_bool v p ->{ sigma }-> sigma'

| e_decl_fun_str : forall v p sigma sigma',
  sigma' = (update_value sigma v p) ->
  decl_fun_string v p ->{ sigma }-> sigma'

| e_decl_main : forall st sigma sigma',
    st -{ sigma }-> sigma' ->
    decl_fun_main st ->{ sigma }-> sigma'
where "G ->{ Sigma }-> Sigma'" := (geval G Sigma Sigma').

Definition ex := main(){'
string' "a" --> "Buna ziua!" 
}'.


Example 
