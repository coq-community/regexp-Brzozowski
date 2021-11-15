(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits. 

Require Import glue gfinset regexp finite_der equiv.
Require Import sim1 sim2.
(* end hide *)
(** Some computation tests *)


Definition V : bregexp := (@Void _).
Definition E : bregexp := (@Eps _).
Definition D : bregexp := (@Dot _ ).
Definition n : seq bregexp := [::].
Definition v : seq bregexp := [:: V].
Definition ve : seq bregexp := [:: V ; E].
Definition eve : seq bregexp := [:: E ; V ; E].
Definition deve : seq bregexp := [:: D ; E ; V ; E].

Definition sim1_dec := sim_dec (@ssim1 [eqType of bool]).
Definition sim2_dec := sim_dec ssim2.

Definition T : bregexp := Atom true.
Definition F : bregexp := Atom false.
Definition SS : bregexp := Conc (Star T) (Star T).
Definition S : bregexp := Star T.



Eval vm_compute in ( (sim1_build_list_fun V V)).
Eval vm_compute in ( (sim1_build_list_fun E V)). 
Eval vm_compute in ( (sim1_build_list_fun E D)). 
Eval vm_compute in ( (sim1_build_list_fun
 (Conc 
  (Atom true) (Conc (Atom false) (Atom true)))
 (Conc 
  (Atom true) (Conc (Atom false) (Atom true))))).
Eval vm_compute in ( (sim1_build_list_fun SS S)).

Eval vm_compute in ( (sim1_build_list_der (Plus (Atom true) (Atom false)))).
Eval vm_compute in ( (sim1_build_list_der (Star (Atom true)))).

Eval vm_compute in
  (sim1_bregexp_eq (Plus (Atom true) (Atom true)) (Atom true)).
Eval vm_compute in
   (sim1_bregexp_eq (Conc (Atom true) V) (And (Atom true) (Atom false))).

Eval vm_compute in ( (sim2_build_list_fun V V)).
Eval vm_compute in ( (sim2_build_list_fun E V)). 
Eval vm_compute in ( (sim2_build_list_fun E D)). 
Eval vm_compute in ( (sim2_build_list_fun
 (Conc 
  (Atom true) (Conc (Atom false) (Atom true)))
 (Conc 
  (Atom true) (Conc (Atom false) (Atom true))))).
Eval vm_compute in ( (sim2_build_list_fun SS S)).

Eval vm_compute in ( (sim2_build_list_der (Plus (Atom true) (Atom false)))).
Eval vm_compute in ( (sim2_build_list_der (Star (Atom true)))).

Eval vm_compute in
  (sim2_bregexp_eq (Plus (Atom true) (Atom true)) (Atom true)).
Eval vm_compute in
   (sim2_bregexp_eq (Conc (Atom true) V) (And (Atom true) (Atom false))).


(** L1 = 0(0+1)*1 *)
Definition L1 := Conc (Atom false)
                 (Conc (Star (Plus (Atom false) (Atom true)))
                 (Atom true)).
(** L2 = 00*1(0+1)* *)
Definition L2 := Conc (Atom false) (Conc (Star (Atom false)) (Conc (Atom true) (Star (Plus (Atom false) (Atom true))))).

Eval vm_compute in 
 (sim1_bregexp_sub (Conc (Atom true) (Atom true)) (Star (Atom true))). 
Eval vm_compute in 
 (sim1_bregexp_sub (Star (Atom true)) (Conc (Atom true) (Atom true))).

Eval vm_compute in 
 (sim2_bregexp_sub (Conc (Atom true) (Atom true)) (Star (Atom true))). 
Eval vm_compute in 
 (sim2_bregexp_sub (Star (Atom true)) (Conc (Atom true) (Atom true))).

Time Eval vm_compute in (sim1_bregexp_sub L1 L2).
Time Eval vm_compute in (sim2_bregexp_sub L1 L2).


Definition L3 := Conc (Atom true) (Star (Conc (Atom false) (Atom true))).
Definition L4 := Conc (Star (Conc (Atom true) (Atom false))) (Atom true).

Time Eval vm_compute in (sim1_bregexp_eq L3 L4).
Time Eval vm_compute in (sim2_bregexp_eq L3 L4).


Definition L5 := And L1 (Not L2).
Time Eval vm_compute in (sim1_bregexp_eq L5 V).
Time Eval vm_compute in (sim2_bregexp_eq L5 V).

Definition K1 := Conc (Atom false) (Plus (Conc (Atom false) (Conc (Star (Atom false)) (Star (Atom true)))) (Star (Atom true))).
Definition K2 := Conc (Atom false) (Conc (Star (Atom false)) (Star (Atom true))).

Time Eval vm_compute in (sim1_bregexp_sub K1 K2).
Time Eval vm_compute in (sim2_bregexp_sub K1 K2).

Definition a := Conc (Atom false) (Atom false).
Definition b := Conc (Atom false) (Atom true).
Definition c := Conc (Atom true) (Atom false).
Definition d := Conc (Atom true) (Atom true).

(**  a*b(c+da*b)* = (a+bc*d)*bc* *)
Definition K3  := 
 Conc (Star a) (Conc b (Star (Plus c (Conc d (Conc (Star a) b))))).
Definition K4 := 
  Conc (Star (Plus a (Conc b (Conc (Star c) d)))) (Conc b (Star c)).

Time Eval vm_compute in (sim1_bregexp_eq K3 K4).
Time Eval vm_compute in (sim2_bregexp_eq K3 K4).


(** forall n >= 8, exists x y,  n = 3 x + 5 y *)
Fixpoint unary (n:nat) : bregexp := match n with
 | O => (@Eps _)
 | Datatypes.S p => Conc (unary p) F
end.


Definition eight := unary 8.
Definition three := unary 3.
Definition five  := unary 5.

Definition M1 := Conc eight (Star F).
Definition M2 := Star (Plus three five).
Time Eval vm_compute in (sim1_bregexp_sub M1 M2).
Time Eval vm_compute in (sim2_bregexp_sub M1 M2).
