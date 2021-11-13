(* begin hide *)
Require Import glue.
From Coq Require Import RelationClasses Setoid Morphisms SetoidList Mergesort Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import bigop path.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SetTheory.
(* end hide *)
Variable A:Type.

(** In this file, I redefine some parts of Ensembles.v 
    it was not mandatory, more an exercise to learn 
    ssreflect's syntax *)

Definition gset := A -> Prop.
Definition grel := A -> A -> Prop.
 
(** Relation tools *)
Definition r_incl (r1 r2 : grel) := forall x y, r1 x y -> r2 x y.
Definition r_not (r:grel) : grel := fun x y => ~ r x y.
Definition r_inter  (r1 r2: grel) : grel := fun x y => r1 x y /\ r2 x y.
Definition r_union (r1 r2: grel) : grel :=
  fun x y =>  r1 x y \/ r2 x y.



Definition Empty_gset :gset := fun _ => False.

Definition Intersection (B C:gset) : gset :=
  fun x: A =>  B x /\ C x.

Definition Union (B C: gset) : gset :=
  fun x:A => B x \/ C x.

Lemma Empty_gset_inv : forall x, ~ Empty_gset x.
Proof.
by move => x; case.
Qed.


Fixpoint prodn (T:Type) (n:nat) : Type := match n with
 | O => unit
 | S p => (T * prodn T p)%type
end.

Fixpoint Finite_Union (n:nat) : prodn  gset n -> gset :=
  match n with
  |O => fun _  => Empty_gset 
  | S p => fun es => let (hd,tl) := es in Union hd (Finite_Union  tl)
end.

Fixpoint pred_prodn (T:Type) (P:T -> Prop) (n:nat) : prodn T n ->  Prop := 
 match n  with
  | O => fun _ => True
  | S p => fun Es => let (hd,tl) := Es in P hd /\ pred_prodn P tl
end.

Definition Included (E F: gset) := forall x, E x -> F x.

Variable R : grel.
Variable E : gset.

(** Accessibility predicate modified to work with an explicit gset *)
Inductive Acc (E:gset) (R:grel) (x:A) : Prop :=
  Acc_intro : (forall y, E y -> R y x -> Acc E R y) -> Acc E R x.


Definition well_founded := forall a: A, Acc E R a.


Fixpoint guard n (wfR: well_founded): well_founded :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro (fun y _ _ => guard n (guard n wfR) y)
  end.


End SetTheory.


Section ExtendedSetTheory.

Variable A B : Type.

(** Definition of [E] = gpred_list E *)
Definition gpred_list  (E: gset A ) : gset (seq A)  := 
 fix aux l : Prop :=
  match l with
  | nil => True
  | x :: xs =>  E x /\ aux xs
end.

(* begin hide *)
Fixpoint tool_list_to_prodn  (E:gset A) (R:grel A) (xs: seq A) : prodn (gset (seq A)) (size xs) :=
 match xs with
  | nil => tt
  | hd :: tl => pair (gpred_list (Intersection E (R hd))) (tool_list_to_prodn E R tl)
end.
(* end hide *)

Lemma gpred_list_inter : forall E1 E2 l, gpred_list E1 l -> gpred_list E2 l -> 
  gpred_list  (Intersection  E1 E2) l.
Proof.
move => E1 E2. elim => [ | hd tl ih] //=.
move  => [h1 h1'] [h2 h2'].
split. by split.  by apply: ih.
Qed.

Lemma gpred_list_cat : forall l1 l2 (E:gset A), (gpred_list E l1 /\ gpred_list E l2) <-> gpred_list E (l1++l2).
Proof.
elim => [ | hd tl  hi] l2 E //=; split => //.
- by case.
- case => [[h1 h2]] h3; split => //. case: (hi l2 E) => h _. by apply: h.
- case => h1 h2. case: (hi l2 E) => _ h. split. split => //. by apply h. by apply h.
Qed.


Lemma gpred_list_incl : forall (E F:gset A), 
 (forall (x:A), F x -> E x) -> forall (l:seq A), gpred_list F l -> gpred_list E l.
Proof.
move => E F h. elim => [ | hd tl hi] //= [hin hpred].
split. by apply: h. by apply: hi.
Qed.

Definition r_prod Ra Rb : grel (A*B) := fun x y => let (a,b) := x in
  let (a',b') := y in (Ra a a') \/ (Rb b b').


Definition Prod (E:gset A) (F:gset B) : gset (A*B) :=
  fun x => let (a,b) := x in  E a /\ F b.


Definition grel_list (R:grel A) : grel (seq A) :=
  fix aux l : seq A -> Prop :=
    match l with
     | nil => fun _ => False
     | x::xs => Union (gpred_list (R x)) (aux  xs)
end.


End ExtendedSetTheory.

Section BarDef.
Variable A:Type.

Variable R: grel A.

(** Main definition for our of inductively finite predicate.
    Bar is no longer relevant, but we kept it since the idea
    comes from Bar induction *)
Inductive Bar (e: gset A ) : Prop :=
 | cBar : (forall x:A, e x -> Bar (Intersection  e (R x))) -> Bar e.
End BarDef.

(** General facts about Bar, which works for any relation *)
Section BarFacts.
Variable A:Type.

Lemma Bar_gset_incl : forall (F:gset A)  (R:grel A), Bar R F -> 
   forall (E:gset A) , Included E F -> Bar R E.
Proof.
move => f R. elim => [F hp hi] E hIncl. clear f.
apply: cBar => a hIna.
apply: (hi a). by apply :hIncl.
move => x [h1 h2].  split => //. by apply: hIncl.
Qed.
(* begin hide *)
Lemma Bar_Empty_gset: forall R:grel A,  Bar R (@Empty_gset A).
Proof.
move => R. apply : cBar => a ha. 
by case: (@Empty_gset_inv A a).
Qed.
(* end hide *)

Lemma Bar_grel_incl : forall E (R R':grel A), Bar R E -> r_incl R' R -> Bar R' E.
Proof.
move => e R R'. elim => [E hp hi] hincl. clear e.
apply cBar => a ha. apply : (@Bar_gset_incl  (Intersection E (R a))).
by apply: hi.
move => x [h1 h2]. split => //.
move: (hincl a) => hh. by apply : hh.
Qed.


Lemma Bar_gset_union: forall (E:gset A) (R:grel A),  Bar R E ->
   forall (F:gset A), Bar R F ->  Bar R (Union E F).
Proof.
move => e R. elim => [E hp hi]; clear e.
move => f. elim => [F hp2 hi2]; clear f.
apply cBar => a. case => ha.
- apply: (@Bar_gset_incl  (Union (Intersection E (R a)) F)).
  by apply: hi. move => x [ [] ].
  move => h1 h2. left. by split.
  move => h1 h2. by right.
- apply: (@Bar_gset_incl (Union E (Intersection F (R a)))).
  by apply: hi2. move => x [[] ]. 
  move => h1 h2. by left.
  move => h1 h2. right. by split.
Qed.

Lemma Bar_grel_union : forall (E:gset A) (R1 R2 :grel A), 
   Bar R1 E -> Bar R2 E -> Bar (r_union R1 R2) E.
Proof.
move => e R1 R2. elim => [e' hp hi]; clear e.
move => h. elim :h hp hi => [E hp2 hi2] hp hi; clear e'.
apply cBar => a ha. apply: (@Bar_gset_incl (Union (Intersection E (R1 a)) (Intersection E (R2 a)))).
apply: Bar_gset_union.
  + apply: hi ; [done | ]. apply: (@Bar_gset_incl E). apply cBar => b hb. by apply: hp2.
    by move => x [].
  + apply: hi2 ; first done. move => x [h1 h2]. apply : (@Bar_gset_incl   (Intersection E (R1 x))).
    by apply: hp.  move => y [[] ]. by split.
    move => x [h1 h2] hB. apply: (@Bar_gset_incl  (Intersection E (R1 x))). apply: hi; first done.
    apply: (@Bar_gset_incl  E). by apply:cBar. by move => x' [].
    by move => y [ [] ]; split.
move => x [h1 []].
move => hr1; left. by split. move => hr2; right. by split.
Qed. 

Lemma Finite_Union_is_finite : forall (R:grel A) (n:nat) (Es: prodn (gset A) n), 
  pred_prodn (Bar R) Es -> Bar  R (Finite_Union Es).
Proof.
move => R. elim => [ | p hi] /=. 
- move => _ _ . by apply: Bar_Empty_gset.
- move => [e Es] [h1 h2]. apply: Bar_gset_union ; first done.
  by apply: hi.
Qed.


End BarFacts.

Section BarFacts_Extended.
Variable A B : Type.

Lemma Bar_gpred_grel : forall  (R:grel A) (E:gset A), Bar  R E -> 
  Bar (grel_list R) (gpred_list E).
Proof.
move => R e. elim => [E hp hi]; clear e.
apply cBar => xs hxs.
apply: (@Bar_gset_incl _  (Finite_Union (tool_list_to_prodn E R xs))). 
apply: Finite_Union_is_finite.
elim : xs hxs => [ | hd tl Ihxs]  /=; first done. case  => hhd htl.
split. by apply: hi.  by apply: Ihxs.
clear hp hi. move => y [hy ]. elim : xs hxs => [ | hd tl hi] //=.
case => hhd htl [ | ]. move => hy2. left.
by apply: gpred_list_inter. move => hrel; right.
by apply: hi.
Qed.


Lemma Bar_gset_prod: forall (E:gset A) (Ra:grel A) (Rb: grel B), Bar Ra E -> forall F, Bar Rb F -> 
  Bar (r_prod Ra Rb) (Prod   E F).
Proof.
move => e Ra Rb. elim => [ E hp hi] f. elim => [ F hp2 hi2]. clear f e.
apply cBar => [[a b] [h1 h2]].
apply: (@Bar_gset_incl _ (Union (Prod (Intersection E (Ra a)) F) (Prod E (Intersection F (Rb b))))).
apply: Bar_gset_union. by apply : hi. by  apply : hi2.
clear hp hi hp2 hi2. case => x y [] [hp1 hp2] [hL | hR].
left. by split. 
right; by split.
Qed.


(* I put it here so that it is correctly generalized according to A *)
(** Tool for one of the main property of Inductively Finite set *)
Lemma lemma6_prime2 : 
 forall E R (x:A), Acc E R x -> 
 Bar (fun x y => R y x) (Intersection E (R^~ x)).
Proof.
move => E R x'. elim => [x hP hi]; clear x'.
apply: cBar => y. case => h1 h2.
apply : (@Bar_gset_incl _ (Intersection E (R^~ y))).
- by apply: hi. move => a [] [ha1 ha2] ha3.
by split.
Qed.

End BarFacts_Extended.

(** From now on, we are working with a relation of equality:
    it has to be a decidable equivalence.
    However we do not require that the equality is substitutive 

    Bar neq E == E is inductively finite
*)

Section INA.
Variable A: Type.
Variable eqA : grel A.

Fixpoint INA (l : seq A) (a : A) : Prop :=
 match l with
 | [::] => False
 | hd :: tl => eqA a hd \/ INA tl a
end.

(** Kuratowski finite:
exists x1...xn, s.t. for all x, 
  E x <-> x =A x1 \/ x =A x2 \/ ... \/ x =A xn
*)
Definition KFinite (E : gset A) : Prop :=
 exists l, (forall x:A, E x <-> INA l x).
Definition neq : grel A := fun x y =>  ~ eqA x y.

(** Inductively finite *)
Definition IFinite E := Bar neq E.
End INA.

Section EqDec.
Variable A:Type.
Variable eqA : grel A.
Context `{Equivalence A eqA}.
Variable eqA_dec : forall (x y:A), {eqA x y}+{ ~ eqA x y }.


(** nR l l' ==  there is x \in l s.t. x \notin l' *)
Definition nR : grel (seq A) := grel_list  (neq eqA). 
Definition nS : grel (seq A) := fun l l' => nR l' l. 

(** Decidable predicate of list membership *)
Fixpoint InA (l:seq A) (a:A) : bool :=
 match l with
 | nil => false
 | x :: xs => if eqA_dec a x then true else InA xs a
end.

Lemma InA_hd : forall a l, InA (a::l) a.
Proof.
move => a l /=.
case: (eqA_dec a a) => //=.
by case; reflexivity.
Qed.

Lemma InA_tl : forall a b l, InA l a -> InA (b::l) a.
Proof.
move => a b l h /=.
by case: (eqA_dec a b).
Qed.
 
Lemma InA_cat : forall l l' x, InA (l++l') x = InA l x || InA l' x.
Proof.
elim => [ | hd tl hi] l' x //=.
by case: (eqA_dec x hd) => h //=.
Qed.

(**
    This hypothesis means that E is compatible with the equality eqA.
    We need something like it to prove that 
     if x \InA l and l \subset E then x \in E
*)
Definition E_compat (E:gset A) := forall x y, eqA x y -> E x -> E y.

Lemma gpred_listP : forall E l (H:E_compat E), gpred_list E l <-> (forall x, InA l x -> E x).
Proof.
rewrite /E_compat. move => E. elim => [ | hd tl hi] HE //=; split.
- case => hhd htl x. case: (eqA_dec x hd) => //=. move => heq _. apply : (@HE hd x) => //. by symmetry.
  move => _. by apply hi.
- move => h; split. apply:h . case: (eqA_dec hd hd) => //=.
  by case; reflexivity.
  apply hi. exact HE. move => z hz. apply: h. by case: (eqA_dec z hd).
Qed.

Lemma gpred_list_notinP : forall (l:seq A)  a, 
  reflect  (gpred_list (neq eqA a) l) (~~ InA l a).
Proof.
elim => [ a | hd tl hi a]  //=. by apply (iffP idP).
apply (iffP idP).
- case: (eqA_dec a hd) => //=. move => hn1 hn2.  split => //.
  by apply/hi.
- move => [ h1 h2]. case: (eqA_dec a hd) => /=. move => h. by case: h1.
  move => h. by apply/hi.
Qed.

Lemma InA_eq : forall l x y, eqA x y -> InA l x = InA l y.
Proof.
elim => [ | a tl hi] x y hxy //=.
case: (eqA_dec x a) => //=. 
- move => hxa. case: (eqA_dec y a) => //=.
  case.  transitivity x => //. by symmetry. 
- move => hneq. case: (eqA_dec y a) => //=. 
  move => hya; case: hneq. by transitivity y.
  move => _; by rewrite (hi x y hxy). 
Qed.


(**
    lots of inversion and decidability lemmas for the several
   equality/inclusion/negation of ... that we need *)
Lemma nR_elim : forall l l',  (nR l l') <-> (exists2 x: A, InA l x  & ~~ InA l' x).
Proof.
elim => [ | hd tl ih] /= l'; split => //. by case.
case.
- move/gpred_list_notinP => hpred.  
  exists hd => //.  by apply: InA_hd. 
- move => hr. case: (ih l') => h _.  case: (h hr) => b h1 h2.
  exists b => //. by case: (eqA_dec b hd) => /=.
- case => b. case: (eqA_dec b hd) => /=.
  move => hbhd _. move/negP => hn. left. apply/gpred_list_notinP. apply/negP. move => h.
  apply: hn. by  rewrite (InA_eq l' hbhd). 
  move => hn_bhd hin hneq. right. apply/ih. by exists b.
Qed.

(** a function eversion of nR *)
Fixpoint Inl_notl' (l l': seq A) : bool :=
  match l with
  | [::] => false
  | hd :: tl => match InA l' hd with
     | true => Inl_notl' tl l'
     | false => true
     end
  end.

Lemma Inl_notl'P : forall l l', reflect (nR l l') (Inl_notl' l l').
Proof.
move => l l'. apply : (iffP idP).
- move => h. apply/nR_elim. elim : l l' h => [ | hd tl hi] l' //=. 
  case_eq (InA l' hd) => //=. move => hIn1 hIn2.
  case: (hi l' hIn2) => a ha1 ha2. exists a => //. by case: (eqA_dec a hd) => //=.
  move => hIn _. exists hd. case: (eqA_dec hd hd) => //=. 
  case; by reflexivity. by rewrite hIn.
- case/nR_elim => a. elim: l => [ | hd tl hi] //=.
  case: (eqA_dec a hd) => //=. move => heq _ hnIn.
  case_eq (InA l' hd) => //=. move => hIn. move/negP: hnIn. case. 
  by rewrite (InA_eq l' heq). 
  move => hneq hIn hnIn. case_eq (InA l' hd) => hIn2 //.
  by apply: hi.
Qed.

Lemma nS_elim : forall l l', (nS l l') <-> (exists2  x, InA l' x & ~~ InA l x).
Proof.
move => l l'. rewrite /nS. apply: nR_elim.
Qed.

Lemma nS_nR_In : forall l l', nS l l' <-> nR l' l.
Proof.
done.
Qed.

Lemma nR_dec  : forall x y, {nR x y} +{~ nR x y}.
Proof.
rewrite /nR. elim => [ | hd tl ih] /= y. by right.
case: (ih y) => [heq | hneq]. by left; right.
case_eq (InA y hd) => h. right.
case. by apply/gpred_list_notinP.
by apply : hneq. left. left. apply/gpred_list_notinP.
by rewrite h.
Qed.

Lemma nS_dec : forall x y, {nS x y} + { ~ nS x y}.
Proof.
move => x y.
elim: (nR_dec y x) => h. by left. by right.
Qed.


Lemma R_elim : forall l l', (r_not nR) l l' <-> (forall x, InA l x-> InA l' x).
Proof.
rewrite /r_not. move => l l'; split => h.
- move => x hx. case_eq (InA l' x)=> heq => //. case: h.
  apply/nR_elim. exists x => //. by rewrite heq.
- move/nR_elim => [b h1]. move/negP =>  h2. apply: h2. by apply :h .
Qed.

Lemma S_elim : forall l l', (r_not nS) l l' <-> forall x, InA  l' x -> InA l x.
Proof.
move => l l'; split.
move => h. apply/R_elim.  rewrite /r_not. move => hn. apply: h. by rewrite nS_nR_In. 
move/R_elim => h. move => hn. apply: h. by rewrite -nS_nR_In.
Qed.

(* begin hide *)
Lemma tool_converse : forall S, r_incl S (r_union (r_inter S (r_not nR)) nR).
Proof. 
rewrite /r_union. move => S x y hxy.
case: (nR_dec x y) => [heq | hneq].
by right. left. by split.
Qed. 
(* end hide *)

(** This is an equality over list stated by "double inclusion":
    eql l1 l2 == forall x, x is in l1 iff x is in l2
*)
Definition eql : grel (seq A) := r_inter (r_not nR) (r_not nS).
Definition neql : grel (seq A) := r_union nR nS.

Lemma eql_dec : forall l l', {eql l l'}+{~eql l l'}.
Proof.
move => l l'. rewrite /eql. case: (nR_dec l l') => h.
right. case => h1 _. by apply:h1.
case: (nS_dec l l') => h'. right. case => _. by apply.
left. split => hn. by apply: h. by apply: h'.
Qed.

Lemma eql_elim : forall l l', eql l l' <-> forall x, (InA l x <-> InA l' x).
Proof.
move => l l'; split. case. move/R_elim => h1. move/S_elim => h2.  move => x; split.
by apply: h1. by apply :h2.
move => h. split. apply/R_elim => x hx. case: (h x).  move => h' _. by apply: h'.
apply/S_elim => x hx. case: (h x).  move => _ h'. by apply: h'.
Qed.

Global Instance eql_Eq: Equivalence eql.
Proof.
split. 
- move => l; by apply/eql_elim.
- move => l l'; move/eql_elim => h. apply/eql_elim => x; split; by move/h.
- move => l l' l''; move/eql_elim => h. move/eql_elim => h'. apply/eql_elim => x; split.
  move/h. by move/h'.   move/h'. by move/h.
Qed.

Lemma neql_elim : forall l1 l2, neql l1 l2 <-> 
  (exists a, (InA l1 a && ~~ InA l2 a) \/ ( ~~ InA l1 a && InA l2 a)).
Proof.
rewrite /neql. move => l1 l2; split.
case. case/nR_elim  => a h1 h2.  exists a; left. by apply/andP.
case/nS_elim => b h1 h2. exists b; right; by apply/andP.
case => a []. case/andP => h1 h2. left. apply/nR_elim. by exists a.
case/andP => h1 h2. right.  apply/nS_elim. by exists a.
Qed.

Lemma neql_dec : forall l1 l2, {neql l1 l2}+{~neql l1 l2}.
Proof.
rewrite /neql => x y. case: (nR_dec x y) => h. by left; left.
case: (nS_dec x y) => h'. by left; right. 
right. case => hu. by apply : h. by apply: h'.
Qed.

(* some implications to check that neql is really the negation 
   of eql. It will be usefull in the main developpment *)
Lemma neql2n_eql : forall l1 l2, neql l1 l2 -> ~ eql l1 l2.
Proof.
move => l1 l2. case/neql_elim => a [|]. 
- case/andP => h1. move/negP => h2. move/eql_elim => heq.  apply: h2. by apply heq.
- case/andP. move/negP => h1 h2.  move/eql_elim => heq.  apply: h1. by apply heq.
Qed.

Lemma eql2n_neql : forall l1 l2, eql l1 l2 -> ~ neql l1 l2.
Proof.
move => l1 l2 heq hneq. by apply: (@neql2n_eql l1 l2).
Qed.

Lemma n_neql2eql : forall l1 l2, ~ neql l1 l2 -> eql l1 l2.
Proof.
move => l1 l2 hneq. apply/eql_elim => x; split => h.
- case_eq (InA l2 x) => heq2 //=. case: hneq. apply/neql_elim.
  exists x; left. apply/andP ; split => //. by rewrite heq2.
- case_eq (InA l1 x) => heq1 //=. case: hneq. apply/neql_elim.
  exists x; right. apply/andP ; split => //. by rewrite heq1.
Qed.

Lemma n_eql2neql : forall l1 l2, ~eql l1 l2 -> neql l1 l2.
Proof.
move => l1 l2 hneq. case: (neql_dec l1 l2) => h //.
case: hneq. by apply: n_neql2eql.
Qed.

(* begin hide *)

Lemma nS_is_enough: forall E, IFinite eqA E -> 
  Bar nS (gpred_list E) -> 
  IFinite eql (gpred_list E).
Proof.
rewrite /IFinite => E hfE h. 
apply: (@Bar_grel_incl _ _ (r_union nR nS)). 
- apply: Bar_grel_union; last done. 
  by apply: Bar_gpred_grel.
move => x y.
by move/n_eql2neql.
Qed.
(* end hide *)

(** the sub predicate reflect the _strict_ inclusion of lists: 
    l l' <-> l strictly included in l' *)
Definition sub : grel (seq A) := r_inter nS (r_not nR).

Lemma sub_elim : forall l l', sub l l' <-> ((forall x, InA l x -> InA l' x) /\ exists2 y, ~~InA l y & InA l' y).
Proof.
rewrite /sub. move => l l'; split.
- case. move/nS_elim => [b h1 h2]. move/R_elim => h. split => //. by exists b.
- case => h [b h1 h2]. split. apply/nS_elim. by exists b. by  apply/R_elim.
Qed.

(* begin hide *)
(*
Definition choice (l:seq A) (Hlnil:l<>nil) : {x:A |  InA l x}.
case: l Hlnil => // a l h.
exists a => //=. by apply: InA_hd. 
Defined.
*)
Definition list_to_set (l: seq A) : gset A := fun x => InA l x.

Definition unionl (l:seq A) F : gset A := Union (list_to_set l) F.

Section Filter_sim.
Variable P : pred A. 
Variable P_compat : forall x y, eqA x y -> P x = P y.

Lemma mem_filter: forall x l, (InA (filter P l) x) = (P x) && (InA l x).
Proof.
move => x; elim => [ | hd tl ] //=.
- by rewrite andbF.
- case: eqA_dec => /=. 
  + move => heq. rewrite (P_compat heq). 
    case: (P hd) => //=. by case: eqA_dec => //=.
  + case: (P hd) => //=. by case: eqA_dec => //=.
Qed.

End Filter_sim.

Definition lminus l l' := filter ((fun x => ~~InA l' x)) l.

Lemma lminusE : forall l1 l2 x, (InA (lminus l1 l2) x) = (~~ InA l2 x) && (InA l1 x).
Proof.
rewrite /lminus => l1 l2 x. rewrite mem_filter => //. 
move => a b heq. by rewrite (InA_eq l2 heq).
Qed.

Lemma lminus_pred: forall P l1 l2, gpred_list P l1 -> gpred_list P (lminus l1 l2).
Proof.
move => P. elim => [ | hd tl hi] l2 //=.
case => hhd htl. case: (InA l2 hd) => //=.
- by apply: hi.
- by split => //; apply: hi.
Qed.

Lemma sub_not_empty : forall l l', sub l l' -> lminus l' l <> nil.
Proof.
move => l l'. move/sub_elim => [ _ [a h1 h2] ] heq.
have h : (InA (lminus l' l) a). rewrite lminusE. by apply/andP; split.
move: h. by rewrite heq. 
Qed.

(* As for Bar, we should find better names for the following lemmas *)
Lemma tool6 : forall F, IFinite eqA F ->
  forall X E, Included E (unionl X F) ->
  E_compat E -> Bar sub (Intersection (gpred_list E) (sub X)).
Proof.
move => f. elim => [F hp hi] X E hincl hE. clear f.
apply:cBar => Y. case => hpred.
move/sub_elim=> [hsub1 hsub2].
case: hsub2 => x0 hx0 heq.
have hincl2 : Included E (unionl Y (Intersection F (neq eqA x0))).
- move => x hx.   have := hincl x hx. case.
  move => hXx. left. by apply: hsub1.
  case: (eqA_dec x x0) => h. move=> hF. left. rewrite /list_to_set.
  by rewrite (InA_eq Y h). 
  move => hF. right. split => //. move => hh; apply: h. by symmetry.
apply : (@Bar_gset_incl _  (Intersection (gpred_list E) (sub Y))). 
apply:(hi x0) => //.
have hEx0 : E x0. move/gpred_listP : hpred.  by apply.
have  := hincl x0 hEx0.  case =>// hF.
move/negP : hx0. by case.  
move => L. case => [[h1 h2]] h3. by split.
Qed.
(*end hide *)

(** sup X Y means Y strictly included in X *)
Definition sup := fun x y => sub y x.

(** If E is inductively finite, then sup is wellfounded on [E] *)
Lemma wf_sup : forall E , E_compat E ->  IFinite eqA E ->
  well_founded sup (gpred_list E).
Proof.
move => E hE.
have htemp : forall F, IFinite eqA F -> 
  forall X, Included E (unionl X F) ->   Acc (gpred_list E) sup X.
- move => f. elim => [F hp hi] X hincl; clear f.
  apply :Acc_intro => Y hpred.
  case/sub_elim => hsub1 hsub2.
  case: hsub2 => x0 hx0 heq.
  have hincl2 : Included E (unionl Y (Intersection F (neq eqA x0))).
  + move => x hx. have := hincl x hx.  case => hu. 
    * left. by apply: hsub1. 
    case: (eqA_dec x x0) => h.  
    * left. by rewrite /list_to_set (InA_eq Y h). 
    right. split => //. move => hh; apply h. by symmetry.
  apply: (hi x0) => //. 
  have hEx0 : E x0.
  + move/gpred_listP : hpred. by apply. 
  have := hincl x0 hEx0.  case => hu //.
  move/negP : hx0. by case. 
move => hE2 X. apply: (htemp E) => //. move => x hx. by right.
Qed.

(** The converse: if sub is wellfounded, then E is inductively finite
    (as in Tarsky's finite set definition) *)
Lemma sup_wf : forall E,  
  well_founded sup (gpred_list E) -> IFinite eqA E. 
Proof.
move => E.
have: forall X, Acc (gpred_list E) sup X -> gpred_list E X ->
      IFinite eqA (Intersection E (fun x =>~ (list_to_set X) x)).
- move => x.
  elim => X hacc hi hp; clear x.
  apply cBar => x0 hx0.
  apply (@Bar_gset_incl  _ 
    (Intersection E (fun x : A => ~ list_to_set (x0::X) x))).
  case: hx0 => hx1. rewrite /list_to_set; move/negP =>  hx2.
  + apply: hi => //=.
    apply/sub_elim; split.
    * move => a ha; by apply : InA_tl.
    exists x0; [by rewrite hx2 | by rewrite InA_hd].
  move => a [[h1 h2] h3].
  split => //.
  rewrite /list_to_set /=.
  case: eqA_dec => //= heq.
  by move => _; apply: h3; symmetry.
move => htemp hwf.
apply: (@Bar_gset_incl _ (Intersection E (fun x : A => ~ false))).
- by apply: (htemp [::]).
by move => a ha.
Qed.

Theorem IFinite_supwf : forall E, E_compat E ->
  (IFinite eqA E <-> well_founded sup (gpred_list E)).
Proof.
move => E hE; split => h.
- by apply wf_sup.
by apply sup_wf.
Qed.


(* begin hide *)
Lemma lemma6 : forall E, E_compat E -> IFinite eqA E ->
  Bar sub (gpred_list  E).
Proof.
move => E hE hfE.
have h : Bar sub (Intersection (gpred_list E) (sub nil)).
- apply : (@tool6 E) =>//. move => x hx. by right. 
apply cBar => y hP. apply: lemma6_prime2. by apply: wf_sup.
Qed.

(* end hide *)
(** An important lemma: 
    if E is finite, then [E] is finite *)
Lemma Bar_gpred_list : forall E, 
  E_compat E -> IFinite eqA E -> IFinite eql (gpred_list  E).
Proof.
move => E hE hfE. apply: nS_is_enough ; first done.
apply: (@Bar_grel_incl _ _ (r_union   (r_inter  nS (r_not   nR)) nR)).
apply: Bar_grel_union.  by apply: lemma6. by apply: Bar_gpred_grel.
by apply :tool_converse.
Qed.

(* begin hide *)
Definition r_subset := (r_not nR).

(* another formulation of subset with a fixpoint + spec *)
Fixpoint sim_incl (l l' : seq A) : bool :=
 match l with
  | [::] => true
  | hd :: tl => 
  match sim_incl tl l' with
     | true => InA l' hd
     | false => false
     end
  end.

Lemma sim_incl_cons : forall hd tl l, sim_incl (hd::tl) l =
  (InA l hd) && sim_incl tl l.
Proof.
move => hd tl l /=. case: (sim_incl tl l).
- by rewrite andbT.
- by rewrite andbF.
Qed.

Lemma sim_incl_cat : forall l1 l2 l, sim_incl (l1++l2) l = sim_incl l1 l && sim_incl l2 l.
Proof.
elim => [ | hd tl hi] l2 l //=. rewrite (hi l2 l).
case: (sim_incl tl l) => //=.
case: (sim_incl l2 l). by rewrite andbT. by rewrite andbF.
Qed.

Lemma sim_inclP : forall l l', reflect (r_subset l l') (sim_incl l l').
Proof.
move => l l'. apply: (iffP idP). 
- move => h. apply/R_elim.
  elim: l l' h => [ | hd tl hi] l' //=. move: (hi l').
  case_eq (sim_incl tl l') => hsim //= hnil.
  move : (hnil (refl_equal true) hd) => //.
  case_eq (InA l' hd) => heq //= hIn _ x.
  case: (eqA_dec x hd) => //=.
  * move => heq2 _. by rewrite (InA_eq l' heq2). 
  * move => _ hin2. by apply: hi.
- move/R_elim. elim: l l' => [ | hd tl hi] l' //= h.
  move: (hi l'). case_eq (sim_incl tl l') => hsim //=.
  * move => _. apply: h. by apply: InA_hd.  
  * apply => x hx. apply: h. by case: (eqA_dec x hd).
Qed.


Lemma sim_incl_InA : forall x l1 l2, InA l1 x -> sim_incl l1 l2 -> InA l2 x.
Proof.
move => x l1 l2. elim : l1 => [ | hd tl] //=. 
case: (sim_incl tl l2) => //=.
case: (eqA_dec x hd) => //=.
- move => heq _ _ hIn. by rewrite (InA_eq l2 heq).
- move => _ h hIn _. by apply: h.
Qed.

Lemma sim_incl_trans : forall l2 l1 l3, sim_incl l1 l2 -> sim_incl l2 l3 ->
  sim_incl l1 l3.
Proof.
move => l2 l1 l3. elim: l1  => [ | hd tl ]  //=.
case: (sim_incl tl l2) => //=.
move: (@sim_incl_InA hd l2 l3).
case: (sim_incl l2 l3) => //=.
by move => h -> // hIn _.
Qed.


Lemma sim_incl_cons2 : forall l l' a, sim_incl l l' -> sim_incl l (a::l').
Proof.
move => l l' a. elim : l => [ | hd tl] //=.
case: (sim_incl  tl l') => //=.
move => -> //. by move => hIn; case_eq (eqA_dec hd a).
Qed.

Lemma sim_incl_cat2l : forall l l' k, sim_incl l l' -> sim_incl l (l'++k).
Proof.
move => l l' k; elim : l => [ | hd tl ] //=.
case: (sim_incl tl l') => //=.
move => -> //. rewrite InA_cat.
by move => ->.
Qed.

Lemma sim_incl_cat2r : forall l l' k, sim_incl l l' -> sim_incl l (k++l').
Proof.
move => l l'; elim => [ | hd tl hi] //= h.
by apply: sim_incl_cons2; apply: hi.
Qed.

Lemma sim_incl_refl : forall l, sim_incl  l l.
Proof.
elim => [ | hd tl hi] //=.
rewrite (sim_incl_cons2 hd hi).
by apply: InA_hd.
Qed.

Lemma sim_incl_lcongr : forall l l' k, sim_incl l l' -> sim_incl (k++l) (k++l').
Proof.
move => l l' k hl. elim: k => [ | hd tl hi] //=.
rewrite (sim_incl_cons2 hd hi).
by apply: InA_hd. 
Qed.


Lemma sim_incl_rcongr : forall l l' k, sim_incl l l' -> sim_incl (l++k) (l'++k).
Proof.
move => l l' k hl. elim: k => [ | hd tl] //=.
- by rewrite ! cats0.
- move/sim_inclP. move/R_elim => hs.
  apply/sim_inclP; apply/R_elim => x. move : (hs x); clear hs. 
  rewrite !InA_cat /=. case: (eqA_dec x hd) => //=.
  by move => _ _ _; rewrite orbT.
Qed.

Lemma lminus_incl : forall l1 l2, sim_incl l2  (l1 ++ (lminus l2 l1)).
Proof.
move => l1; elim => [ | hd tl] //=.  case_eq (InA l1 hd) => /=. 
- move => hIn ->. by rewrite InA_cat hIn. 
- move => hIn. move/sim_inclP.  move/R_elim => hincl.
  case_eq (sim_incl tl (l1 ++ hd :: lminus tl l1)) => /=.
  +  move => _. rewrite InA_cat. by rewrite InA_hd orbT.  
  +  case/sim_inclP.  apply/R_elim => x0 hx0. move : (hincl x0 hx0).
     rewrite !InA_cat /=.   case/orP => -> //=. 
     by case: eqA_dec => /= ; rewrite orbT.
Qed.



Lemma r_subset_dec : forall X Y, {r_subset X Y} + {~r_subset X Y}.
Proof.
move => X Y.
case_eq (sim_incl X Y). move/sim_inclP => h. by left.
move/sim_inclP => h. by right => h'; apply: h.
Qed.
(* end hide *)

(** building of the fixpoint 
    first version of build list, but not the one we really use
    since we need a tweaked version. I leave it as a comment in the code
*)
Theorem build_list : forall E, E_compat E -> IFinite eqA E -> 
  forall (G:seq A -> seq A)
  (HG1: forall X, r_subset X (G X)) (HG2: forall X, (gpred_list E) X -> (gpred_list E) (G X)),
  forall X, (gpred_list E) X -> { Y | r_subset X Y /\ (gpred_list E) Y /\ r_subset (G Y) Y }.
Proof.
move => E hE hfE G hG1 hG2 X hX.
have h: Acc (gpred_list E) sup X. by apply: wf_sup.
elim: h hX=> Y hp hi hX. clear X. rename Y into X. elim: (r_subset_dec (G X) X) => hsub.
- exists X; split. by apply/R_elim.  by split.
- case: (hi (G X)).
  * by apply: hG2.
  * apply/sub_elim. split. apply/R_elim. by apply :hG1.
    elim: (nR_dec (G X) X) => [| hneq]. move/nR_elim => [a h1 h2]. by exists a.
    elim: hsub. move => hn. elim: hneq. done.
  * by apply: hG2.
  * move => Y [h1]. move/R_elim:h1 => h1. move => [h2]. move/R_elim => h3. exists Y; split.
    apply/R_elim.  move => x hx. apply: h1. move/R_elim : (hG1 X). by apply.
    split. done. by apply/R_elim.
Qed.

(* begin hide *)               

(* Annexe about equality on lists:
   there is two equality on lists, the point wise equality (defined inductively)
   and the double inclusion. In the previous part, they were called
   eq_list and eql.

  In the main developpment, we will need to go from one equality to the other
  which is not possible in the general case: eq_list -> eql is true, but the 
  other is not usually valid. This is only true if the lists
  are strictly sorted (sorted without duplicates).

  This was already proven by Pierre Letouzey in the SetoidList.v file of
  Coq's stdlib (where they are named eqlistA and equivlistA).

  ==> The following lemmas are the glue to switch from list to seq and seq to
       list.
*)
Variable ltA : grel A.
Context `{StrictOrder A ltA}.

Variable ltA_proper : Proper (eqA ==> eqA ==> iff) ltA.
Definition Sorteds l := Sorted ltA (seq_to_list l).

Definition InA2 := SetoidList.InA eqA.

Lemma InA2P : forall x l, reflect (InA2 x (seq_to_list l)) (InA l x).
Proof.
move => x l; apply: (iffP idP).
- elim :l => [ | hd tl hi]//=. case: (eqA_dec x hd) => heq /=.
  move => _ .  apply SetoidList.InA_cons. by left. move => hIn. apply SetoidList.InA_cons.
  by right; apply: hi.
- remember (seq_to_list l) as L. move => hIn. move: l HeqL. elim: hIn => /=; clear L.
  move => y l heq [ // | a l'] /=. case => hhd htl. case: (eqA_dec x a) => //=.
  elim. by rewrite -hhd. move => y l hIn hi [ // | a l'] /=. case => hhd htl.
  case: (eqA_dec x a) => //=. move => _ . by apply : hi.
Qed.
  
Lemma eql_iff_list : forall s s', eql s s' <-> equivlistA eqA (seq_to_list s) (seq_to_list s').
Proof.
move => s s'; split.
- move/eql_elim => heql. rewrite /equivlistA. move => x; split => h.
  apply/InA2P. apply heql. by apply/InA2P.   
  apply/InA2P. apply heql. by apply/InA2P. 
- rewrite /equivlistA => heq. apply/eql_elim => x; split => h.
    apply/InA2P. apply heq. by apply/InA2P.   
    apply/InA2P. apply heq. by apply/InA2P.
Qed.

Fixpoint eq_list (s s':seq A) {struct s} : bool := match s,s' with
 | nil,nil => true
 | hd::tl , hd'::tl' => if eqA_dec hd hd' then eq_list tl tl' else false
 | _ , _ => false
end.

Lemma InA_eq2 : forall l l' x, eq_list l l' -> InA l x = InA l' x.
Proof.
elim. by case => //=.
move => hd tl hi. case => //=. move => hd' tl' x.
case: (eqA_dec hd hd') => //= heq1 htl.
case: (eqA_dec x hd) => //=. move => heq .
case: (eqA_dec x hd') => //=. case. by transitivity hd.
move => hneq. case: (eqA_dec x hd') => //=.  move => heq2.
case: hneq. transitivity hd' => //.  by symmetry. 
move => hn; by apply: (hi tl' x).
Qed.


Global Instance eq_list_Eq : Equivalence eq_list.
Proof.
split.
- elim => [ | hd tl hi] //=. case: (eqA_dec hd hd) => //=. case; by reflexivity. 
- elim => [ | hd tl hi] [ | hd2 tl2] //=. case: (eqA_dec hd hd2) => //=.
  move => heq1 heq2. case: (eqA_dec hd2 hd) => //=. move => _; by apply: hi. 
  case; by symmetry.
- elim => [ | hd tl hi] [ | hd2 tl2] [ | hd3 tl3] //=.
  case: (eqA_dec hd hd2) => //=. move => heq1 heq2.
  case: (eqA_dec hd2 hd3) => //=. move => heq3 heq4. 
  case: (eqA_dec hd hd3) => //=. move => _; by apply: (hi tl2 tl3).
  case; by transitivity hd2.
Qed.


Definition ldisjoint l l' := eq_list (lminus l l') l.

Lemma ldisjointP : forall l1 l2, reflect
 (forall x, InA l1 x -> InA l2 x -> False)
 (ldisjoint l1 l2).
Proof.
rewrite /ldisjoint => l1 l2; apply: (iffP idP).
- move => hm x. rewrite -(InA_eq2 x hm).
  rewrite lminusE. case/andP => h1 h2 h3. move: h1.
  by rewrite h3.   
- elim: l1 => [ | hd tl hi] h //=. move: (h hd).
  rewrite InA_hd.
  case: (InA l2 hd) => /=.
  by case;  reflexivity.
  case: (eqA_dec hd hd) => //=.
  move => _ _.  apply: hi => // x h1 h2.
  apply: (h x) => //=. by case: eqA_dec. 
  case; by reflexivity.
Qed.

Lemma ldisjoint_lminus: forall l1 l2, ldisjoint l1 (lminus l2 l1).
Proof.
move => l1 l2; apply/ldisjointP => x hx. rewrite lminusE.
case/andP => hn hx2. move/negP : hn. by apply.
Qed.



Lemma eql_eq_list : forall l l', eq_list l l' -> eql l l'.
Proof.
elim => [ | hd tl hi] [ | hd' tl'] //=.
- move => _; by reflexivity.
- case: (eqA_dec hd hd') => //=.
- move => heq1 heq2. apply eql_elim => x; split => /=.
  * case : (eqA_dec x hd) => h1 /=. case: (eqA_dec x hd')=> //=. case. by rewrite h1.
    case: (eqA_dec x hd')=> //=. move => hneq hIn. rewrite (@InA_eq2 tl' tl x) => //.  by symmetry. 
  * case : (eqA_dec x hd') => h1 /=. case: (eqA_dec x hd)=> //=. case. transitivity hd' => //.
    by symmetry.  case: (eqA_dec x hd)=> //=. move => hneq hIn. by  rewrite (@InA_eq2 tl tl' x) => //.  
Qed.



Lemma eq_list_iff_list : forall s s',  eqlistA eqA (seq_to_list s) (seq_to_list s') -> eq_list s s'. 
Proof.
elim => [ | hd tl hi] [ | hd' tl'] //=.
- move => h; inversion h.
- move => h; inversion h.
- move => h; inversion h; subst; clear h. case: (eqA_dec hd hd') => //=. 
  move => _; by apply: hi. 
Qed. 

Lemma eq_list_eql_Eq : forall (l l': seq A), Sorteds l -> Sorteds l' -> eql l l' ->  eq_list l l'.
Proof.
move => l l' hS1 hS2. move/eql_iff_list => heql. apply eq_list_iff_list.
by apply: SortA_equivlistA_eqlistA.
Qed.

Lemma Permutation_InA2 : forall l l' x, Permutation l l' -> InA2 x l -> InA2 x l'.
Proof.
move => l l' x h. move: x. elim : h => //=; clear l l'.
- move => x l l' h hi y. case/SetoidList.InA_cons. move => ->. by apply/SetoidList.InA_cons; left; reflexivity.
  move => h'. apply/SetoidList.InA_cons; right. by apply hi.
- move => x y l a. case/SetoidList.InA_cons. move => ->. apply/SetoidList.InA_cons; right. by apply/SetoidList.InA_cons; left; reflexivity.
  case/SetoidList.InA_cons. move => ->. by apply/SetoidList.InA_cons; left; reflexivity. move => h; apply/SetoidList.InA_cons; right.
  by apply/SetoidList.InA_cons; right.
- move => l1 l2 l3 hperm1 hi1 hperm2 hi2 a hIn. by apply: hi2 ; apply: hi1.
Qed.
  
Lemma neqs_perm : forall l l' k k', Permutation (seq_to_list l) (seq_to_list l') ->
  Permutation (seq_to_list k) (seq_to_list k') -> neql l k -> neql l' k'.
Proof.
move => l l' k k' hP1 hP2. case/neql_elim => a [ | ].
- case/andP => h1 h2. apply/neql_elim; exists a; left; apply/andP ; split.
  apply/InA2P. apply Permutation_InA2 with (seq_to_list l) => //. by apply/InA2P.
  move/negP: h2 => h2. apply/negP => h3. apply : h2. 
  apply/InA2P. apply Permutation_InA2 with (seq_to_list k'). by symmetry. by apply/InA2P.
- case/andP => h1 h2. apply/neql_elim; exists a; right; apply/andP ; split.
  move/negP: h1 => h1. apply/negP => h3. apply : h1. 
  apply/InA2P. apply Permutation_InA2 with (seq_to_list l'). by symmetry. by apply/InA2P.
  apply/InA2P. apply Permutation_InA2 with (seq_to_list k) => //. by apply/InA2P.
Qed.


End EqDec.
(* end hide *)

(** Another major result:
   if f is compatible with eqA and eqB (which is x =A y -> (f x) =B (f y))
   and E/=A is inductively finite, then (f E)/=B is inductively finite
*)
Section Result.
Variable A:Type.
Variable B:Type.
Variable eqA: grel A.
Variable eqB: grel B.
Context `{Equivalence A eqA}.
Context `{Equivalence B eqB}.


Definition eq_prod : grel (A*B) := fun x y => let (a,b) := x in
  let (a',b') := y in (eqA a a' /\ eqB b b').

Global Instance eq_prod_Eq : Equivalence eq_prod.
Proof.
split.
- case => /=. by move => a b ; split; reflexivity.
- case => a b [a' b'] [ha hb].  split; by symmetry.
- case => a b [a' b'] [a'' b''] [ha hb] [ha' hb']; split.
  by transitivity a'.   by transitivity b'.
Qed.



Lemma eq_prod_dec :(forall x y, {eqA x y}+{~eqA x y}) -> (forall x y, {eqB x y}+{~eqB x y}) ->
  forall x y, {eq_prod x y}+{~eq_prod x y}.
Proof.
rewrite /eq_prod => hA hB [a b] [a' b'].
case: (hA a a') => hA'. case: (hB b b') => hB'.
by left; split. right. case => _ hn. by apply: hB'.
right. case => hn _. by apply: hA'.
Defined.

Lemma InA_inv : forall (T:eqType) (eqT: grel T) (hE: Equivalence eqT) 
  (hdec: forall x y, {eqT x y}+{~eqT x y}),
 forall Y e, InA hdec Y e -> exists2 f, (f \in Y) & eqT f e.
Proof.
move => T eqT hE hdec. elim => [ | hd tl hi] e //=.
case: (hdec e hd) => //=.
- move => heq _. exists hd. by rewrite in_cons; apply/orP; left.
  by symmetry.
- move => _ h. case: (hi e h) => f h1 h2. exists f => //.
  by rewrite in_cons h1 orbT.
Defined. 


(* end hide *)
Variable f : A -> B.
Definition f_set (E: gset A) : gset B := fun y => exists2 x, E x & eqB (f x) y.
Variable f_compat : forall a a', eqA a a' -> eqB (f a) (f a').

Lemma Bar_fun : forall E , IFinite eqA E -> IFinite eqB (f_set E).
Proof.
move => e. elim => [E hp hi]. clear e.
apply:  cBar => y. case => x h1 h2.
apply: (@Bar_gset_incl _ (f_set (Intersection E (neq eqA x)))).
by apply: hi.
move => b [[a ha1 ha2] hb].
exists a => //. split => //.  move => hxa. apply: hb.
transitivity (f x). by symmetry. transitivity (f a) => //.
by apply: f_compat.
Qed.

  
End Result.
