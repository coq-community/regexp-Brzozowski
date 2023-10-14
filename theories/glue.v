(* begin hide *)
From Coq Require Import Mergesort Permutation.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(* end hide *)

(** Definition of the [eqType] structure of the 3 states type [comparison] *)

Lemma comparison_negK : forall s t, s = CompOpp t -> t = CompOpp s.
Proof. by case => [] []. Qed.

Definition eq_comparison (a b:comparison) : bool :=
match a,b with
 | Lt,Lt => true
 | Eq,Eq => true
 | Gt,Gt => true
 | _,_ => false
end.

Lemma eq_comparison_axiom : Equality.axiom eq_comparison.
Proof.
move => a b. apply: (iffP idP).
by case : a b => [] [].
by move => ->; case :b .
Qed.

HB.instance Definition _ := hasDecEq.Build comparison eq_comparison_axiom.

(** Definition of a canonical structure of an eqType with a 3 states
    total comparison function *)
Record osym_module_mixin (char:eqType) : Type := OSymModuleMixin {
  cmp : char -> char -> comparison;
  cmp_refl : forall s, cmp s s = Eq;
  cmp_eq_axiom : forall s t, reflect (s = t) (cmp s t == Eq);
  cmp_trans : forall (s t u:char) (x:comparison),
    cmp s t = x -> cmp t u = x -> cmp s u = x;
  cmp_neg : forall (s t:char), cmp t s = CompOpp (cmp s t)
}.

Record osym_module : Type := OSymModule {
  carrier :> eqType;
  spec : osym_module_mixin carrier
}.

Definition cmpS (s:osym_module) := cmp (spec s).
Definition leS (S:osym_module) :=
 fun (x y:S) => if cmpS x y is Gt then false else true.

Lemma cmpS_refl : forall (S:osym_module) (b:S), cmpS b b = Eq.
Proof. by move => S b; rewrite /cmpS cmp_refl. Qed.

Lemma cmpS_eq_axiom : forall (S:osym_module) (a b:S),
 reflect (a = b) (cmpS a b == Eq).
Proof.
move => S a b. rewrite /cmpS. by apply: cmp_eq_axiom.
Qed.

Lemma cmpS_trans : forall (S:osym_module) (a b c:S) (x: comparison),
 cmpS a b = x -> cmpS b c = x -> cmpS a c = x.
Proof.
move => S a b c x.
rewrite /cmpS => h1 h2. by apply  (@cmp_trans _ _ a b c).
Qed.

Lemma cmpS_neg : forall (S:osym_module) (a b: S),
  cmpS a b = CompOpp (cmpS b a).
Proof.
move => S a b. by rewrite /cmpS cmp_neg.
Qed.

Lemma leS_refl : forall (S:osym_module), reflexive (@leS S). 
Proof.
rewrite /leS => S a. by rewrite cmpS_refl.
Qed.

Lemma leS_trans : forall (S:osym_module), transitive (@leS S). 
Proof.
rewrite /leS => S b a c. case_eq (cmpS a b) => // hc1 _.
- case_eq (cmpS b c) => // hc2 _. by rewrite (cmpS_trans hc1 hc2).
  move/eqP: hc1. move/cmpS_eq_axiom. move => ->. by rewrite hc2.
- case_eq (cmpS b c ) => // hc2 _. move/eqP: hc2. move/cmpS_eq_axiom. 
  by move => <-; rewrite hc1.
by rewrite (cmpS_trans hc1 hc2).
Qed.

Lemma leS_antisym : forall (S: osym_module), antisymmetric (@leS S).
Proof.
rewrite /leS => S a b. rewrite cmpS_neg. case_eq (cmpS b a) => //=.
move/eqP. move/cmpS_eq_axiom. by move => <-.
Qed.

Lemma leS_total : forall (S:osym_module), total (@leS S).
Proof.
rewrite /leS => S a b. rewrite cmpS_neg. by case: (cmpS b a).
Qed.

(** Some very general definitions and missing 
    properties in ssreflect stdlib *)
Section Glue.

Variables A B : Type.

Lemma flatten_map_cons (l:seq A) :
 flatten [seq (cons^~ [::]) i | i <- l] = l.
Proof.
elim: l => [ | hd tl ih] //=. by rewrite {1}ih.
Qed.

Definition dupl (X: seq (A*B)) : seq (A*A*B) :=
  map (fun (ab:A*B) => let (a,b) := ab in (a,a,b)) X.

Definition strip (X: seq (A*A*B)) : seq (A*B) :=
  map (fun (ab:A*A*B) => let (aa,b) := ab in let (a,_) := aa in (a,b)) X.

Lemma dupl_strip : forall (X:seq (A*B)), strip (dupl X) = X.
Proof.
by elim => [|[hda hdb] tl hi] //=; rewrite hi.
Qed.

End Glue.

Section Glue2.

Variables T T' : eqType.
Variable R : rel T.

Lemma tool_undup_size : forall (l l': seq T), size (undup l') <= size (undup (l++l')).
Proof.
elim => [ | hd tl hi] l' //=. case: (hd \in tl ++ l') => //=.
by apply (@leq_trans (size (undup (tl++l')))).
Qed.

Lemma tool_undup_size2 : forall (l l': seq T), size (undup l) <= size (undup (l++l')).
Proof.
move => l l'. rewrite (@perm_size _ (undup (l ++ l')) (undup (l'++l))).
by apply tool_undup_size. apply uniq_perm. by apply undup_uniq. by apply undup_uniq.
move => u. rewrite !mem_undup !mem_cat. by apply orbC.
Qed.

Lemma merge_sort_sym : forall (hR1:transitive R) (hR2: antisymmetric R) (hR3: total R)
 (l1 l2:seq T), sorted R l1 -> sorted R l2 -> merge R l1 l2 = merge R l2 l1.
Proof.
move => hR1 hR2 hR3 l1 l2 h1 h2; apply (sorted_eq hR1 hR2).
- by apply merge_sorted.
- by apply merge_sorted.
- by rewrite perm_merge perm_sym perm_merge perm_catC.
Qed.

Lemma tool_normP_in : forall (hd:T) tl l, perm_eq (hd::tl) l ->
 exists l1, exists l2, l = l1 ++ hd :: l2 /\ tl =i l1 ++ l2.
Proof.
move => hd tl l hp.
have hs: (splitr hd l).
- apply: splitPr. rewrite -(perm_mem hp). by rewrite in_cons eq_refl.
case: hs hp => l1 l2 hp.  exists l1; exists l2;  split => //.
apply: perm_mem. move: hp.
by rewrite -[hd :: l2]cat1s perm_sym perm_catCA /= perm_cons perm_sym.
Qed.

(** boolean operator to check inclusion of lists:
    lincl l l' means that forall x in l, x is in l'
*)

Fixpoint lincl (l l':seq T) : bool :=
match l with
 | [::] => true
 | hd :: tl => (hd \in l') && (lincl tl l')
end.

Lemma linclP l l' : reflect {subset l <= l'} (lincl l l').
Proof.
apply: (iffP idP).
- elim: l => [|hd tl hi] //=.
  case/andP => hhd htl a; rewrite in_cons.
  case/orP => hu; last by apply: hi.
  by rewrite (eqP hu).
- elim: l => [|hd tl hi] //= h.
  apply/andP; split; first by apply: h; rewrite in_cons eq_refl.
  apply/hi => a h'; apply: h.
  by rewrite in_cons h' orbT.
Qed.

Lemma lincl_cons : forall (l l1:seq T) a, lincl l l1 -> lincl l (a::l1).
Proof.
elim => [ | hd tl hi] l1 a //=.
case/andP => hhd hdtl. apply/andP; split.
by rewrite in_cons hhd orbT. by apply: hi.
Qed.

Lemma lincl_catr : forall (l l1 l2: seq T), lincl l l1 -> lincl l (l1 ++ l2).
Proof.
elim => [ | hd tl hi] l1 l2 //=.
case/andP => hhd htl. by rewrite mem_cat hhd; apply : hi.
Qed.

Lemma lincl_refl : forall (l:seq T), lincl l l.
Proof.
elim => [ | hd tl hi] //=. apply/andP; split.
- by rewrite in_cons eq_refl.
- by apply: lincl_cons.
Qed.

Lemma lincl_nil : forall (l:seq T), lincl l [::] -> l = [::].
Proof. by case.  Qed.

Lemma lincl_trans : transitive lincl.
Proof.
rewrite /transitive => y.
elim => [ | hd tl hi] z //=.
case/andP => hhd htl hincl.
rewrite (hi z htl hincl) andbT /=.
move/linclP : hincl.  by apply. 
Qed.

Lemma strip_in : forall (X: seq (T*T*T')) (a a':T) (b:T'), 
  (a,a',b) \in X -> (a,b) \in (strip X).
Proof.
elim => [ | [[hd1 hd2] hdb] tl hi] //= a a' b.
rewrite !in_cons. case/orP.
- rewrite eqE /=. case/andP. case/andP => /= heq _ heq2.
  by rewrite (eqP heq) (eqP heq2) eq_refl.
- move => h. by rewrite (hi a a' b h) orbT.
Qed.

End Glue2.
