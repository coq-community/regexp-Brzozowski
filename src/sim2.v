(* begin hide *)
From Coq Require Import RelationClasses Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
Require Import glue regexp finite_der equiv.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits. 
(* end hide *)

(** This implementation of similarity is more effiencient than
     sim1. The main idea is to compile the regular expression
     in a form where the similarity is the _syntactic_ equality.

     We also inforce more simplification than Brzozosky to speed up
     the test:
       - A + A ~ A, A + B ~ B + A, A + (B + C) ~ (A + B) + C
       - A & A ~ A, A & B ~ B & A, A & (B & C) ~ (A & B) & C
       - A** = A, empty* = epsilon
       - eps.A ~ A.eps ~ A, empty.A ~ A.empty ~ empty, A.(B.C) ~ (A.B).C
       - not not A ~ A

     This is done by the canonical_regexp structure, and the use of 
     smart constructors which preserves these invariants
*)

Section RegExpSim. 


Variable symbol : osym_module.
Let regexp := regular_expression symbol.
Let word := word symbol.
Let Void := Void symbol.
Let Eps := Eps symbol.
Let Dot := Dot symbol.

(** An alternative presentation of regexp that enjoys a simple
   ordering, and thus are more easily checked for equality 
   The idea is to store striclty sorted lists to avoid rewriting
   rules such as r + s ~ s + r or (a + b) + c ~ a + (b + c)
*)

Inductive canonical_regexp :=
 | CVoid
 | CEps
 | CDot
 | CAtom of symbol
 | CStar of canonical_regexp
 | CPlus of seq canonical_regexp
 | CAnd of seq canonical_regexp
 | CConc of seq canonical_regexp 
 | CNot of canonical_regexp.

(* begin hide *)
Implicit Type r : canonical_regexp.

(* Alternative induction scheme for canonical regexp *)
Section creg_ind.
Variables (P: canonical_regexp -> Prop) (Q: seq canonical_regexp -> Prop).

Hypotheses (HVoid : P CVoid)
           (HEps : P CEps)
           (HDot : P CDot)
           (HAtom: forall s, P (CAtom s))
           (HStar : forall c, P c -> P (CStar c))
           (HPlus: forall l, Q l -> P (CPlus l))
           (HAnd: forall l,  Q l -> P (CAnd l))
           (HConc: forall l, Q l -> P (CConc l))
           (HNot : forall c, P c -> P (CNot c))
           (H0 : Q [::])
           (H1: forall c, P c -> forall l, Q l -> Q (c::l)).

Fixpoint creg_ind (c:canonical_regexp) : P c :=
 match c as xx return P xx with
  | CVoid => HVoid
  | CEps => HEps
  | CDot => HDot
  | CAtom s => HAtom s
  | CStar c1 => HStar (creg_ind c1)
  | CPlus l => HPlus 
     ((fix aux (l': seq canonical_regexp) : Q l' :=
         match l' as yy return Q yy with
           | [::] => H0
           | hd :: tl => H1  (creg_ind hd)  (aux tl)
           end) l)
  | CAnd l => HAnd  
     ((fix aux (l': seq canonical_regexp) : Q l' :=
         match l' as yy return Q yy with
           | [::] => H0
           | hd :: tl => H1  (creg_ind hd)  (aux tl)
           end) l)
  | CConc l => HConc  
     ((fix aux (l': seq canonical_regexp) : Q l' :=
         match l' as yy return Q yy with
           | [::] => H0
           | hd :: tl => H1  (creg_ind hd)  (aux tl)
           end) l)
  | CNot c1 => HNot (creg_ind c1)
end.
End creg_ind.

(* Translation function from canonical regexp to usual regexp *)
Fixpoint creg_to_reg r : regexp :=
 match r with
  | CVoid => Void
  | CEps => Eps
  | CDot => Dot
  | CAtom x => Atom x
  | CStar r1 => Star (creg_to_reg r1)
  | CPlus l => foldr (fun xx yy => Plus xx yy) Void 
     (map creg_to_reg l)
  | CAnd l => foldr (fun xx yy => And xx yy) (Not Void) 
     (map creg_to_reg l)
  | CConc l => foldr (fun xx yy => Conc xx yy) Eps 
     (map creg_to_reg l)
  | CNot r1 => Not (creg_to_reg r1) 
end.

(* This function computes the language associated to a canonical regexp
   by computing the language of its translation to usual presentation *)
Definition mem_creg r := mem_reg (creg_to_reg r).

Canonical Structure can_reg_exp_predType := PredType mem_creg.
(* end hide *)


(* begin hide *)

(* Same as has_eps for canonical regexp (mainly for testing purpose) *)
Fixpoint has_eps_can r :=
  let fix hec_forall l : bool := match l with
 |  [::]  => true
 |  hd :: tl => (has_eps_can hd) && (hec_forall tl)
end in  
  let fix  hec_exists  l : bool := match l with
 | [::] => false
 | hd :: tl => (has_eps_can hd) || (hec_exists tl)
end in
 match r with
  | CVoid => false
  | CEps => true
  | CDot => false
  | CAtom _ => false
  | CStar _ => true
  | CPlus l => hec_exists l
  | CAnd l => hec_forall l 
  | CConc l =>  hec_forall l
  | CNot r1 => ~~  (has_eps_can r1)
end.


Fixpoint hec_forall l : bool := match l with
 | [::] => true
 | hd :: tl => has_eps_can hd && hec_forall tl
end.

Fixpoint hec_exists  l : bool := match l with
 | [::] => false
 | hd :: tl => (has_eps_can hd) || (hec_exists tl)
end.


Lemma has_eps_canE : forall r, has_eps_can r = ([::] \in r) .
apply creg_ind with (fun l => 
  hec_forall l = (all (fun xx => [::] \in xx) l)/\
  hec_exists l = (has (fun xx => [::] \in xx) l)).
+ done.
+ done.
+ done.
+ by move => s.
+ by move => c.
+ move => l [ _ hl ] /= ; move : hl. rewrite /hec_exists ; move => ->. 
  rewrite  -topredE /= /mem_creg /=.  by elim: l => [ | hd tl hi] //=; rewrite hi.
+ move => l [ hl _ ] /= ; move : hl. rewrite /hec_forall ; move => ->. 
  rewrite  -topredE /= /mem_creg /=.  by elim: l => [ | hd tl hi] //=; rewrite hi.
+ move => l [ hl _ ] /= ; move : hl. rewrite /hec_forall ; move => ->.
  rewrite  -topredE /= /mem_creg /=.  elim: l => [ | hd tl hi] //=. apply/andP/concP. 
  * case => hhd hall. exists [::] => //.
    exists [::] => //.  by rewrite -topredE /= /mem_creg /= -hi.
  * case => [v1 hv1 [v2 hv2 ]]. case: v1 hv1 => //= hv1 heq.
    by rewrite hv1 hi heq.
+ by move => c h /= ; rewrite h.
+ done.
+ move => c hc l [hl1 hl2] /=; split.
  - by congr andb. 
  - by congr orb.
Qed.
(* end hide *)

(** Smart constructor for the Kleene Star operator *)
Definition mkStar r := match r with
 | CEps => CEps
 | CVoid => CEps
 | CStar _ => r
 |  _ => CStar r
end.

(* Proof that the smart constructor is correct *)
Lemma mkStar_mem : forall r, CStar r =i mkStar r.
Proof.
move => r. elim: r => //=.
- move => u. rewrite -topredE /= /mem_creg /=. rewrite !inE. 
  apply/starP/idP.
  move => [[ | hd tl]] /=. move => _ ->. done.
  rewrite andbF //=. 
  * move => heq. rewrite (eqP heq). exists [::]. done. done.
- move => u. rewrite -topredE /= /mem_creg /=. rewrite !inE. 
  apply/starP/idP.
  * move => [v]. elim: v => [ | hd tl hi] /=. by  move => _ ->.
    move/andP  => [].  move/andP =>[].  move/negP.  done.
    move => heq. rewrite (eqP heq). by exists [::].
   move => c h. move => u. rewrite -!topredE /= /mem_creg /=.
   rewrite -[star _ _]/(_ \in star _). by rewrite star_id.
Qed.

(** total comparison function on canonical regexp *)
Fixpoint compare r1 r2 {struct r1} : comparison := 
 let fix compareList l1 l2 {struct l1} : comparison := match l1,l2 with
 | [::],[::] => Eq
 | [::], _ => Lt
 | _, [::] => Gt
 | a1 :: t1, a2 :: t2 => match compare a1 a2 with
       | Eq => compareList t1 t2
       | o => o
       end
  end in match r1,r2 with
 | CEps, CEps => Eq
 | CEps, _ => Lt
 | _, CEps => Gt
 | CDot, CDot => Eq
 | CDot, _ => Lt
 | _, CDot => Gt
 | CVoid , CVoid => Eq
 | CVoid, _ => Lt
 | _, CVoid => Gt
 | CAtom a, CAtom b => cmpS a b
 | CAtom a, _ => Lt
 | _, CAtom b => Gt
 | CConc l1, CConc l2 => compareList l1 l2
 | CConc _ , _ => Lt
 | _, CConc  _ => Gt
 | CStar r1, CStar r2 => compare r1 r2
 | CStar r1, _=> Lt
 | _, CStar r2 => Gt
 | CPlus l1, CPlus l2 => compareList l1 l2
 | CPlus _ , _ => Lt
 | _, CPlus _ => Gt
 | CAnd l1, CAnd l2 => compareList l1 l2
 | CAnd _ , _ => Lt
 | _, CAnd  _ => Gt
 | CNot a, CNot b => compare a b
  end.


Fixpoint compareList l1 l2 {struct l1} : comparison := match l1,l2 with
 | [::],[::] => Eq
 | [::], _ => Lt
 | _, [::] => Gt
 | a1 :: t1, a2 :: t2 => match compare a1 a2 with
       | Eq => compareList t1 t2
       | o => o
       end
  end.

(* begin hide *)

(* Some properties of our compare operator *)
Lemma compare_refl : forall r, compare r r = Eq.
Proof.
apply creg_ind with (fun l => compareList l l = Eq) => //=.
- apply cmpS_refl.
- by move => c1 -> c2 ->.
Qed.

Lemma compareList_refl : forall l, compareList l l = Eq.
Proof.
elim => [ | hd tl hi] //=. by rewrite (compare_refl hd).
Qed.

(* If regexp are Eq than they are syntactically equal *)
Lemma compare_eq_axiom : forall r1 r2, compare r1 r2 = Eq -> r1 = r2.
Proof.
apply (@creg_ind  (fun r1 => forall r2, compare r1 r2 = Eq -> r1 = r2) 
  (fun l => forall l', compareList l l' = Eq -> l = l')).
- by case => //=. - by elim => //=.
- by case => //=.
- move => s; elim => //=. move => s0. move/eqP. move/cmpS_eq_axiom.
  by move => ->.
- move => c hc. elim  => //. move => c2 hc2 heq.
  move : heq => /= heq. by rewrite (hc c2).
- move => l hl. elim => //. move => l' hl'. by  rewrite (hl l').
- move => l hl. elim => //. move => l' hl'. by  rewrite (hl l').
- move => l hl. elim => //. move => l' hl'. by  rewrite (hl l').
- move => c hc. elim  => //. move => c2 hc2 heq.
  move : heq => /= heq. by rewrite (hc c2).
- elim => //=.
- move => c hc l hl. elim => //. move => c' l' hl' heq.
  rewrite (hl l'). rewrite (hc c'). done.
  move : heq => /=. case (compare c c') => //.
  move : heq => /=. case (compare c c') => //.
Qed.

Lemma compareList_eq_axiom : forall l1 l2, compareList l1 l2 = Eq <-> l1 = l2.
Proof.
elim => [ | hd tl hi] [ | hd' tl'] //= ; split.
- have := (@compare_eq_axiom hd hd').   case: (compare hd hd') => //=.
  move => -> //=. case: (hi tl') => hhi _. move => h; by  rewrite  (hhi h).
- case => -> ->. by rewrite compare_refl compareList_refl.
Qed.

(* Our compare is equalivalent to Leibniz equality, so we can build prove
   that canonical_regexp are an instance of eqType *)
Lemma canonical_regexp_eq_axiom : Equality.axiom (fun r1 r2 => compare r1 r2 == Eq).
Proof.
move => r1 r2. apply: (iffP idP).
- move/eqP => h. by apply: compare_eq_axiom.
- move => ->. by rewrite (compare_refl r2).
Qed.

Definition canonical_regexp_eq_mixin := EqMixin canonical_regexp_eq_axiom.

Canonical Structure canonical_regexp_eqType := EqType canonical_regexp canonical_regexp_eq_mixin.

Lemma compare_trans : forall r1 r2 r3 s, compare r1 r2 = s -> compare r2 r3 = s -> compare r1 r3 = s.
Proof.
apply (@creg_ind (fun r1 => forall r2 r3 s, compare r1 r2 = s -> compare r2 r3 = s -> compare r1 r3 = s) 
     (fun l1 => forall  l2 l3 s, compareList l1 l2 = s -> compareList l2 l3 = s -> compareList l1 l3 = s)) => 
      [ | | | s | c hc | l hl | l hl | l hl | c hc  | | hd hc tl htl ] /=.
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //=; by move => s'' <-).
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //=; by move => s'' <-).
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //=; by move => s'' <-).
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //=. by apply cmpS_trans.
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //. by apply:  hc.   
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //. by apply: hl.
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //. by apply: hl.
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //. by apply: hl.
- case =>  [ | | | s' | c'  | l'  | l' | l' | c' ] //=; try (case => //; by move => s1 s2 <-).
  case => //. by apply:  hc.   
(* lists *)
- case => [ | hd tl] //=. case => [ | hd' tl'] //=. by move => s <-.
- case => [ | hd' tl' ] //=. case => [ | hd'' tl''] //= ; by move => s <-.
  case => [ | hd'' tl''] //=. move => s. move: (hc hd' hd'' s); clear hc.
  move: (htl tl' tl'' s); clear htl.  case_eq (compare hd hd') => h1 //=.
  * rewrite (compare_eq_axiom h1).
    by case_eq (compare hd' hd'') => h2 //=. 
  * case_eq (compare hd' hd'') => h2 //=. 
    rewrite -(compare_eq_axiom h2) h1.
    by move => _ _ <- _.    
    move => _ h hs _. move: h. rewrite -hs. 
    by move => ->.
    by move => _ _ <-.
  * case_eq (compare hd' hd'') => h2 //=. 
    rewrite -(compare_eq_axiom h2) h1.
    by move => _ _ <- _.    
    by move => _ _ <-.
    move => _ h hs _. move: h. rewrite -hs. 
    by move => ->.
Qed.


Lemma compareList_trans : forall l1 l2 l3 s, compareList l1 l2 = s -> compareList l2 l3 = s -> compareList l1 l3 = s.
Proof.
elim => [ | hd tl hi] => //=.
- case => [ | hd' tl'] //=. - case => [ | hd'' tl''] //=. by move => s <-.
- case => [ | hd' tl' ] //=. case => [ | hd'' tl''] //= ; by move => s <-.
  case => [ | hd'' tl''] //=. move => s. move: (@compare_trans hd hd' hd'' s).
  move: (hi tl' tl'' s); clear hi.  case_eq (compare hd hd') => h1 //=.
  * rewrite (compare_eq_axiom h1); by case: (compare hd' hd'').
  * case_eq (compare hd' hd'') => h2 //=. 
    rewrite -(compare_eq_axiom h2) h1. by move => _ _ <- _.
    move => _ h hs _. move : h; rewrite -hs.
    by move => ->.
    by move => _ _ <-.
  * case_eq (compare hd' hd'') => h2 //=. 
    rewrite -(compare_eq_axiom h2) h1. by move => _ _ <- _.
    by move => _ _ <-.
    move => _ h hs _. move : h; rewrite -hs.
    by move => ->.
Qed.


Lemma compare_neg : forall c1 c2, compare c2 c1 = CompOpp (compare c1 c2).
Proof.
apply (@creg_ind (fun c1 => forall c2 , compare c2 c1 = CompOpp (compare c1 c2))
      (fun l1 => forall  l2, compareList l2 l1 = CompOpp (compareList l1 l2))) =>
      [ | | | s | c hc | l hl | l hl | l hl | c hc  | | hd hc tl htl ] /=; try (by case => /=).
- case => //= s'. by apply : cmpS_neg.
- case => [ | hd' tl'] //=. move: (hc hd'). case: (compare hd' hd) => h //=. by rewrite (comparison_negK h) /=. 
  by rewrite (comparison_negK h) /=.   by rewrite (comparison_negK h) /=.
Qed.
    
Definition cregexp_osym_module_mixin := OSymModuleMixin compare_refl canonical_regexp_eq_axiom compare_trans compare_neg.
Definition cregexp_osym_module := OSymModule cregexp_osym_module_mixin.

Canonical Structure cregexp_osym_module.


Definition cregexp_le : rel canonical_regexp := @leS cregexp_osym_module.

(* instanciate merge and sort with our order
   TODO: as suggested by Georges, since we handle only sorted
         list, we should not use the undup of ssr but build 
         our own to remove adjacent duplicate (better complexity).
   TODO: I actually did it for Coq list in current2.v, I'll
   	 do it again for seq 
*)

Definition merge' l1 l2 := nosimpl (merge cregexp_le l1 l2).

Definition sort' := fun l => sort cregexp_le l.

(* end hide *)
(** Smart constructor for concatenation:
  mkConc r1 r2 builds a canonical regexp which is equivalent to r1.r2
  but with simplification of its structure (remove epsilon, void, flatten list ... )
*)  

Definition mkConc r1 r2 : canonical_regexp := nosimpl match r1,r2 with
 |  CEps, _ => r2
 | _ , CEps => r1
 | CVoid, _ => CVoid
 | _, CVoid => CVoid
 | CConc l1, CConc l2 => CConc (cat l1 l2)
 | _, CConc l2 => CConc (r1 :: l2)
 | CConc l1, _ => CConc (cat l1 ([:: r2]))
 | _,_ => CConc [:: r1; r2]
end.

(* begin hide *)
Lemma CConcP : forall l1 l2 u,
  reflect (exists2 v1, v1 \in CConc l1 & exists2 v2, v2 \in CConc l2 & u = v1++v2)
     (u \in (CConc (l1++l2))).
Proof.
elim => [ | hd tl ih] l2 u /=;
 rewrite -!topredE /= /mem_creg /=.
- apply: (iffP idP). exists [::] => //.
  exists u => //. case => [v1 hv1 [v2 hv2 heq]].
  case: l2 v2 hv2 heq => [ | hd2 tl2 ] v2 /=.
  *  move: hv1. rewrite -!topredE /= /mem_creg /= /eps /=.
     move => h1 h2 -> ; by rewrite (eqP h1) (eqP h2).
  *  move:hv1; rewrite -topredE /= /mem_creg /=.
     rewrite /eps /=; move=> h. move/concP => [w1 hw1 [ w2 hw2 ->]] ->.
     rewrite (eqP h). apply/concP. exists w1 => //. exists w2 => //.
- apply: (iffP (@concP symbol _ _ _)).
  * case => [v1 hv1 [v2 hv2 -> ]]. case: (ih l2 v2 hv2) => v2' hv2' [v3 hv3] -> .
    exists (v1 ++ v2'). rewrite -topredE /= /mem_creg /=.
    apply/concP. exists v1 => //. by exists v2'. exists v3 => //.
    by rewrite catA.
  * case => [v1]. rewrite -topredE /= /mem_creg /=.
    move/concP => [w1 hw1 [ w2 hw2 ->]]. case => [v2 hv2 ->].
    exists w1 => //. exists (w2++v2). apply/ih.
    exists w2 => //. by exists v2. by rewrite catA.
Qed.

Lemma toolmkConc : forall r, [ \/ r == CVoid , r == CEps , (exists l, r == CConc l) |
     [ /\ r != CVoid , r != CEps & (forall l, r != CConc l) ] ].
Proof.
case => [ | | | s | c | l | l | l | c ] //=; try by apply: Or44.
- by apply: Or41.
- by apply: Or42.
- by apply: Or43; exists l.
Qed.

Lemma mkConc_unfold: forall l r, [/\ r != CVoid, r != CEps & (forall l, r != CConc l) ] ->
  mkConc (CConc l) r = CConc (l++[::r]).
Proof.
move => l. case => [ | | | s | c | l' | l' | l' | c ] //=.
- by case.
- by case.
- case => _ _ h. move/negP:  (h l'). by case.
Qed.

Lemma mkConc_unfold2: forall l r, [/\ r != CVoid, r != CEps & (forall l, r != CConc l) ] ->
  mkConc r (CConc l) = CConc (r::l).
Proof.
move => l. case => [ | | | s | c | l' | l' | l' | c ] //=.
- by case.
- by case.
- case => _ _ h. move/negP:  (h l'). by case.
Qed.

Lemma mkConc_unfold3 : forall r1 r2, [/\ r1 != CVoid, r1 != CEps & (forall l, r1 != CConc l) ] ->
 [/\ r2 != CVoid, r2 != CEps & (forall l, r2 != CConc l) ] ->
  mkConc r1 r2 = CConc [::r1 ; r2].
Proof.
case => [ | | | s | c | l | l | l | c ] /=. 
- by move => r2 [].
- by move => r2 [].
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
- move => r2 [_ _ h]. move/negP: (h l); by case.
- case => [ | | | t | d | k | k | k | d ] //= _.
  by case. by case. case => _ _ h. move/negP: (h k); by case.
Qed.

(* end hide *)
Lemma mkConc_CVoid_lt : forall r, mkConc CVoid r = CVoid.
Proof.
by case.
Qed.

Lemma mkConc_CVoid_rt : forall r, mkConc r CVoid = CVoid.
Proof.
by case.
Qed.

Lemma mkConc_CEps_lt : forall r, mkConc CEps r = r.
Proof.
by case.
Qed.

Lemma mkConc_CEps_rt : forall r, mkConc r CEps = r.
Proof.
by case.
Qed.

(* Proof that the smart constructor has the same behaviour than the usual constructor *)
Lemma mem_mkConc : forall r1 r2, (mkConc r1 r2) =i (CConc [:: r1 ; r2]).
Proof.
move => r1. case: (toolmkConc r1).
- move => heq; rewrite (eqP heq) => r2 u; clear r1 heq.
  rewrite -!topredE /= /mem_creg /=. apply/idP/concP.
  by case: r2 => /=. by case.
- move => heq; rewrite (eqP heq) /= => r2 u; clear r1 heq.
  rewrite -!topredE /= /mem_creg /=. apply/idP/concP.
  move => h; exists nil => //. exists u => //=.
  apply/concP. by exists u => //; exists nil => //; rewrite cats0.
  case => vnil /=. case: vnil => //= _. case => v.
  case/concP => w hw. case. case => //= _. by rewrite cats0 => -> ->.
- case => l heq; rewrite (eqP heq) => r2 u; clear r1 heq. case: (toolmkConc r2).
  * move => heq; rewrite (eqP heq); clear r2 heq.
    rewrite -!topredE /= /mem_creg /=. apply/idP/concP => //.
    case => v h1. case => w. by case/concP.
  * move => heq; rewrite (eqP heq) /=; clear r2 heq.
    rewrite -!topredE /= /mem_creg /=. apply/idP/concP.
    move => h; exists u => //. exists nil => /=. apply/concP.
    exists nil => //. by exists nil => //. by rewrite cats0.
    case => v hv /=. case => vnil. move/concP. case => [ [|] ] //= _. case => [[|]] //= _ -> .
    by rewrite cats0 => ->.
  * case => l' heq; rewrite (eqP heq) /=; clear r2 heq.
    change [:: CConc l; CConc l'] with ([:: CConc l] ++ [:: CConc l']).
    apply/CConcP/CConcP. case => v1 hv1 [v2 hv2 ->]. exists v1.
    rewrite -topredE /= /mem_creg /=. apply/concP. exists v1 => //.
    by exists nil => //; rewrite cats0. exists v2 => //.
    rewrite -topredE /= /mem_creg /=. apply/concP. exists v2 => //.
    by exists nil => //; rewrite cats0.
    case => v1 hv1 [v2 hv2 ->]. exists v1. move: hv1. rewrite -!topredE /= /mem_creg /=.
    case/concP => v hv. case => [[|]] //= _. by rewrite cats0 => ->. move: hv2.
    rewrite -!topredE /= /mem_creg /=. case/concP => v hv. case => [[|]] //= _.
    rewrite cats0 => ->. by exists v.
  * move => h; rewrite mkConc_unfold => //=. change [:: CConc l; r2] with ([:: CConc l]++[::r2]).
    apply/CConcP/CConcP. case => v hv [w hw ->]. exists v. rewrite -topredE /= /mem_creg /=.
    apply/concP. exists v => //. exists nil => //; by rewrite cats0. by exists w.
    case => v hv [w hw -> ]. rewrite -topredE /= /mem_creg /= in hv. case/concP : hv => v' hv' [[|]] //= _.
    rewrite cats0 => ->. exists v' => //=. by exists w => //=.
- move => h0 r2 u. case: (toolmkConc r2).
  * move => heq; rewrite (eqP heq) mkConc_CVoid_rt; clear r2 heq.
    rewrite -!topredE /= /mem_creg /=. apply/idP/concP => //.
    case => v h1. case => w. by case/concP.
  * move => heq; rewrite (eqP heq) mkConc_CEps_rt ; clear r2 heq.
    rewrite -!topredE /= /mem_creg /=. apply/idP/concP.
    move => h; exists u => //. exists nil => /=. apply/concP.
    exists nil => //. by exists nil => //. by rewrite cats0.
    case => v hv /=. case => vnil. move/concP. case => [ [|] ] //= _. case => [[|]] //= _ -> .
    by rewrite cats0 => ->.
  * case => l' heq; rewrite (eqP heq) mkConc_unfold2 //=; clear r2 heq.
    rewrite -!topredE /= /mem_creg /=. apply/concP/concP. 
    case => v hv [w hw ->]. exists v => //. exists w => //. apply/concP.
    exists w => //. by exists nil => //;  rewrite cats0.
    case => v hv [w]. case/concP => w' hw' [[|] //= _ ]. rewrite cats0 => -> ->. 
    exists v => //. by exists w'.
  * move => h1. by rewrite mkConc_unfold3 => //.
Qed.

(** Smart constructor for the Plus operator: the particular point 
   is that it orders the elements from lowest to greatest
   and remove duplicates *)

Definition mkPlus r1 r2 :=  nosimpl match r1,r2 with
 | CVoid, _ => r2
 | _, CVoid => r1
 | CPlus l1, CPlus l2 => match undup (merge' (sort' l1) (sort' l2)) with
     | nil => CVoid 
     | [:: r] => r
     | rs => CPlus rs
     end
  | CPlus l1, _ => match undup (merge' (sort' l1) [::r2]) with
     | nil => CVoid
     | [:: r] => r
     | rs => CPlus rs
     end
  | _, CPlus l2 => match undup (merge' [:: r1] (sort' l2)) with
     | nil => CVoid
     | [:: r] => r
     | rs => CPlus rs
     end
  | _,_ => match compare r1 r2 with
     | Lt => CPlus [:: r1; r2]
     | Eq => r1
     | Gt => CPlus [:: r2; r1]
     end
end.

(* some simplifaction rewrite rules *)
Lemma mkPlus_CVoid_rt : forall r, mkPlus r CVoid = r.
Proof.
by case.
Qed.

Lemma mkPlus_CVoid_lt : forall r, mkPlus CVoid r = r.
Proof.
by [].
Qed.

(* begin hide *)
Lemma mkPlus_congr : forall r1 r2 r3 r4, r1 == r2 -> r3 == r4 -> mkPlus r1 r3 == mkPlus r2 r4.
Proof.
move => r1 r2 r3 r4 h1 h2. by rewrite (eqP h1) (eqP h2).
Qed.

(* some helper function to prove properites of mkPlus *)
Lemma CPlus_cons : forall hd tl u, (u \in CPlus (hd :: tl) )= (u \in hd ) || (u \in CPlus tl).
Proof.
move => hd tl u.
rewrite -!topredE /= /mem_creg /=. by apply/orP/orP.
Qed.

Lemma CPlus_has : forall l u, (u \in CPlus l) = has (fun c => u \in c) l.
Proof.
elim => //=. move => hd tl hi u.
rewrite CPlus_cons. by rewrite hi.
Qed.

Lemma CPlus_undup : forall l, CPlus (undup l) =i CPlus l.
Proof.
move => l u. rewrite ! CPlus_has. apply/hasP/hasP. 
- case => x h1 h2. exists x => //.  by rewrite -mem_undup.
- case => x h1 h2. exists x => //.  by rewrite mem_undup.
Qed.

Lemma CPlus_sort : forall le l, CPlus (sort le l) =i CPlus l.
Proof.
move => le l u. rewrite ! CPlus_has. apply/hasP/hasP. 
- case => x h1 h2. exists x => //. move: h1; by rewrite mem_sort.
- case => x h1 h2. exists x => //.  by rewrite mem_sort.
Qed.

Lemma CPlus_mem_match : forall l1 l2 u, 
 (u \in (match undup (merge' (sort' l1) (sort' l2)) with
     | nil => CVoid
     | [:: r] => r
     | rs => CPlus rs
 end)) = (u \in CPlus (l1 ++ l2)).
Proof.
rewrite /merge' /sort'. move => l1 l2. 
have : (undup (merge' (sort' l1) (sort' l2)) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge  !mem_cat !mem_sort.
case: (undup (merge' (sort' l1) (sort' l2))) => //.
- move => h u. rewrite CPlus_has. by rewrite -(eq_has_r h).
- move => hd0. case => //. move => h u. by rewrite  CPlus_has -(eq_has_r h) has_seq1.
  move => hd tl h u. rewrite !CPlus_has. by rewrite -(eq_has_r h).
Qed.

Lemma CPlus_mem_match1 : forall l1 l2 u, 
 (u \in (match undup (merge' (sort' l1) l2) with
     | nil => CVoid
     | [:: r] => r
     | rs => CPlus rs
 end)) = (u \in CPlus (l1 ++ l2)).
Proof.
rewrite /merge' /sort'. move => l1 l2. 
have : (undup (merge' (sort' l1) l2) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge  !mem_cat !mem_sort.
case: (undup (merge' (sort' l1) l2)) => //.
- move => h u. rewrite CPlus_has. by rewrite -(eq_has_r h).
- move => hd0. case => //. move => h u. by rewrite  CPlus_has -(eq_has_r h) has_seq1.
  move => hd tl h u. rewrite !CPlus_has. by rewrite -(eq_has_r h).
Qed.

Lemma CPlus_mem_match2 : forall l1 l2 u, 
 (u \in (match undup (merge' l1 (sort' l2)) with
     | nil => CVoid
     | [:: r] => r
     | rs => CPlus rs
 end)) = (u \in CPlus (l1 ++ l2)).
Proof.
rewrite /merge' /sort'. move => l1 l2. 
have : (undup (merge' l1 (sort' l2)) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge  !mem_cat !mem_sort.
case: (undup (merge' l1 (sort' l2))) => //.
- move => h u. rewrite CPlus_has. by rewrite -(eq_has_r h).
- move => hd0. case => //. move => h u. by rewrite  CPlus_has -(eq_has_r h) has_seq1.
  move => hd tl h u. rewrite !CPlus_has. by rewrite -(eq_has_r h).
Qed.


Lemma CPlus_cat : forall l1 l2 u, (u \in CPlus (l1++l2)) = (u\in CPlus l1) || (u \in CPlus l2).
Proof.
elim => [ | hd tl hi] l2   //= u.
by rewrite !CPlus_cons (hi l2) orbA.
Qed. 

Lemma CPlus_catC : forall l1 l2, CPlus (l1++l2) =i CPlus (l2++l1).
Proof.
move => l1 l2 u. rewrite !CPlus_cat. by rewrite orbC.
Qed.


(* again, tools to help reduce the size of following proofs (naively, the
   following proof can have up to 9*9*9 cases, this reduce to 3*3*3
   and even few by some use of symmetry *)
Lemma toolmkPlus : forall c, [\/ c == CVoid , (exists l , c == CPlus l) | 
    (c != CVoid /\ (forall l, c != CPlus l)) ].
Proof.
case => [ | | | s | c | l | l | l | c ] //=; try ( by apply Or33;split).
- by apply : Or31.
- by apply : Or32; exists l.
Qed.

Lemma toolmkPlus2_l: forall r,  (r != CVoid /\ (forall l,  r != CPlus l)) ->
 forall l, 
  mkPlus r (CPlus l) = match undup (merge' [::r] (sort' l)) with
                         | [::] => CVoid
                         | [:: c] => c
                         | s => CPlus s
                         end.
Proof.
case => [ | | | s | c | l | l | l | c ] [] //= _.
move => h. move/negP: (h l). by case.
Qed.

Lemma toolmkPlus2_r: forall r, (r != CVoid /\ (forall l,  r != CPlus l)) -> 
 forall l, 
  mkPlus (CPlus l) r = match undup (merge' (sort' l) [::r] ) with
                         | [::] => CVoid
                         | [:: c] => c
                         | s => CPlus s
                         end.
Proof.
case => [ | | | s | c | l | l | l | c ] [] //= _.
move => h. move/negP: (h l). by case.
Qed.

Lemma toolmkPlus3 : forall r1 r2, (r1 != CVoid /\ (forall l, r1 != CPlus l)) ->
  (r2 != CVoid  /\ (forall l, r2 != CPlus l)) ->
  mkPlus r1 r2 =  match compare r1 r2 with
     | Lt => CPlus [:: r1; r2]
     | Eq => r1
     | Gt => CPlus [:: r2; r1]
     end
.
Proof.
case => [ | | | s | c | l | l | l | c ] r2 [] //= _.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- move => h. move/negP: (h l); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ [] //= _. move => h. move/negP : (h k); by case.
Qed.

(* end hide *)

(* Proof that the smart constructor is correct *)
Lemma mem_mkPlus : forall r1 r2, mkPlus r1 r2 =i CPlus [:: r1; r2].
Proof.
move => r1. case: (toolmkPlus r1).
- move => heq r2 u; rewrite (eqP heq) mkPlus_CVoid_lt; clear r1 heq.
  by rewrite !CPlus_cons -[u \in CPlus _]topredE /= /mem_creg /= orbF.
- case => l heq r2 u; rewrite (eqP heq); clear r1 heq. case: (toolmkPlus r2). 
  * move => heq; rewrite (eqP heq) mkPlus_CVoid_rt; clear r2 heq.
    by rewrite !CPlus_cons -[u \in CPlus _]topredE /= /mem_creg /= orbF.
  * case => k' heq; rewrite (eqP heq) /mkPlus !CPlus_cons; clear r2 heq.
    rewrite -[u \in CPlus [::]]topredE /= /mem_creg /= orbF.
    by rewrite CPlus_mem_match CPlus_cat.
  * move => h. rewrite toolmkPlus2_r  ?CPlus_mem_match1 => //.
    by rewrite CPlus_cat !CPlus_cons -![u \in CPlus [::]]topredE /= /mem_creg /= orbF.
- move => h1 r2 u. case: (toolmkPlus r2).
  * move => heq; rewrite (eqP heq) mkPlus_CVoid_rt; clear r2 heq.
    by rewrite !CPlus_cons -[u \in CPlus _]topredE /= /mem_creg /= orbF.
  * case => k' heq; rewrite (eqP heq) toolmkPlus2_l ?CPlus_mem_match2 => //; clear r2 heq.
    by rewrite CPlus_cat !CPlus_cons -![u \in CPlus [::]]topredE /= /mem_creg /= !orbF.
  * move => h. rewrite toolmkPlus3 => //.
    move: (@compare_eq_axiom r1 r2). case : (compare r1 r2) => //.
    move => -> //. rewrite !CPlus_cons -![u \in CPlus [::]]topredE /= /mem_creg /= !orbF.
    by apply/idP/orP; [left | case].
    rewrite !CPlus_cons -![u \in CPlus [::]]topredE /= /mem_creg /= !orbF => _.
    by rewrite orbC.
Qed.

(* begin hide *)
(* helper function to prove properties about mkAnd *)
Lemma CAnd_cons : forall hd tl u, (u \in CAnd (hd :: tl) )= (u \in hd ) && (u \in CAnd tl).
Proof.
move => hd tl u.
rewrite -!topredE /= /mem_creg /=. by apply/andP/andP.
Qed.

Lemma CAnd_all : forall l u, (u \in CAnd l) = all (fun c => u \in c) l.
Proof.
elim => [ | hd tl hi] //= u. 
- rewrite CAnd_cons. by rewrite hi.
Qed.

Lemma CAnd_undup : forall l, CAnd (undup l) =i CAnd l.
Proof.
move => l u. rewrite ! CAnd_all. apply/allP/allP. 
- move => h x hIn; apply h. by rewrite mem_undup.
- move => h x hIn; apply h. by move: hIn; rewrite mem_undup.
Qed.

Lemma CAnd_sort : forall le l, CAnd (sort le l) =i CAnd l.
Proof.
move => le l u. rewrite ! CAnd_all. apply/allP/allP. 
- move => h x hIn; apply h. by rewrite mem_sort.
- move => h x hIn; apply h. by move: hIn; rewrite mem_sort.
Qed.


Lemma flatten_map_cons : forall (A:Type) (l:seq A), flatten (map (fun xx => [::xx]) l) = l.
Proof.
move => A; elim => [ | hd tl ih] //=. by rewrite {1}ih.
Qed.


Lemma in_All : forall u, (u \in Not Void).
Proof.
move => u; rewrite -topredE /=. by apply/negP.
Qed.

Lemma in_All2 : forall u, (u \in Star Dot).
Proof.
elim => [ |hd tl iH] //=.
move/starP : iH => [s h1 h2]. apply/starP.
exists (cat [:: [::hd]]  (map (fun xx => [::xx]) tl)) => //=.
apply/allP => x hx. move/mapP : hx => [y hin hy]. by rewrite hy.
by rewrite flatten_map_cons.
Qed.

Lemma in_CAll : forall u, (u \in CNot CVoid).
Proof.
move => u; rewrite -topredE /= /mem_creg /=.
by apply/negP.
Qed.

Lemma in_CAll2: forall u, (u \in CStar CDot).
Proof.
elim => [ |hd tl iH] //=.
move/starP : iH => [s h1 h2]. apply/starP.
exists (cat [:: [::hd]]  (map (fun xx => [::xx]) tl)) => //=.
apply/allP => x hx. move/mapP : hx => [y hin hy]. by rewrite hy.
by rewrite flatten_map_cons.
Qed.

Lemma in_CAnd_nil : forall u, (u \in CAnd [::]).
Proof.
by move => u; rewrite CAnd_all /=.
Qed.

Lemma CAnd_mem_match : forall l1 l2 u, 
 (u \in (match undup (merge' (sort' l1) (sort' l2)) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
 end)) = (u \in CAnd (l1 ++ l2)).
Proof.
rewrite /merge'. move => l1 l2. 
have : (undup (merge cregexp_le (sort' l1) (sort' l2)) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge !mem_cat !mem_sort.
case: (undup (merge cregexp_le (sort' l1) (sort' l2))) => //.
- move => h u. rewrite CAnd_all. by rewrite -(eq_all_r h) in_CAll.
- move => hd0. case => //. move => h u. by rewrite  CAnd_all -(eq_all_r h) all_seq1.
  move => hd tl h u. rewrite !CAnd_all. by rewrite -(eq_all_r h).
Qed.

Lemma CAnd_mem_match1 : forall l1 l2 u, 
 (u \in (match undup (merge' (sort' l1) l2) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
 end)) = (u \in CAnd (l1 ++ l2)).
Proof.
rewrite /merge'. move => l1 l2. 
have : (undup (merge cregexp_le (sort' l1) l2) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge !mem_cat !mem_sort.
case: (undup (merge cregexp_le (sort' l1) l2)) => //.
- move => h u. rewrite CAnd_all. by rewrite -(eq_all_r h) in_CAll.
- move => hd0. case => //. move => h u. by rewrite  CAnd_all -(eq_all_r h) all_seq1.
  move => hd tl h u. rewrite !CAnd_all. by rewrite -(eq_all_r h).
Qed.

Lemma CAnd_mem_match2 : forall l1 l2 u, 
 (u \in (match undup (merge' l1 (sort' l2)) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
 end)) = (u \in CAnd (l1 ++ l2)).
Proof.
rewrite /merge'. move => l1 l2. 
have : (undup (merge cregexp_le l1 (sort' l2)) =i (l1++l2)).
  by move => u; rewrite mem_undup mem_merge !mem_cat !mem_sort.
case: (undup (merge cregexp_le l1 (sort' l2))) => //.
- move => h u. rewrite CAnd_all. by rewrite -(eq_all_r h) in_CAll.
- move => hd0. case => //. move => h u. by rewrite  CAnd_all -(eq_all_r h) all_seq1.
  move => hd tl h u. rewrite !CAnd_all. by rewrite -(eq_all_r h).
Qed.

Lemma CAnd_cat : forall l1 l2 u, (u \in CAnd (l1++l2)) = (u\in CAnd l1) && (u \in CAnd l2).
Proof.
elim => [|hd tl hi] l2 //= u.
by rewrite !CAnd_cons (hi l2) andbA.
Qed. 

Lemma CAnd_catC : forall l1 l2, CAnd (l1++l2) =i CAnd (l2++l1).
Proof.
move => l1 l2 u. rewrite !CAnd_cat. by rewrite andbC.
Qed.

(* end hide *)
(** Smart constructor for the And operator: as for Plus, it orders the elements
   in the list *)

Definition mkAnd r1 r2 := nosimpl match r1,r2 with
 | CVoid, _ => CVoid
 | _, CVoid => CVoid
 | CNot CVoid, _ => r2
 | _, CNot CVoid => r1
 | CAnd l1, CAnd l2 => match undup (merge' (sort' l1) (sort' l2)) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
     end
  | CAnd l1, _ => match undup (merge' (sort' l1) [::r2]) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
     end
  | _, CAnd l2 => match undup (merge' [:: r1] (sort' l2)) with
     | nil => CNot CVoid
     | [:: r] => r
     | rs => CAnd rs
     end
  | _,_ => match compare r1 r2 with
     | Lt => CAnd [:: r1; r2]
     | Eq => r1
     | Gt => CAnd [:: r2; r1]
     end
end.


Lemma mkAnd_CVoid_rt : forall r, mkAnd r CVoid = CVoid.
Proof.
case => [ | | | s | r1  | l1 | l1 | l1 | r1 ]//=.
by case: r1.
Qed.

Lemma mkAnd_CVoid_lt : forall r, mkAnd CVoid r = CVoid.
Proof.
by [].
Qed.


Lemma mkAnd_CAll_lt : forall r, mkAnd (CNot CVoid) r = r.
Proof.
by case.
Qed.

Lemma mkAnd_CAll_rt : forall r, mkAnd r (CNot CVoid) = r.
Proof.
case => //. by case.
Qed.

(* begin hide *)
Lemma toolmkAnd : forall c, [ \/ c == CVoid , c == CNot CVoid, (exists l , c == CAnd l) | 
   [ /\ c != CVoid , c != CNot CVoid & (forall l, c != CAnd l)]].
Proof.
case => [ | | | s | c | l | l | l | c ]; try (by apply Or44).
- by apply Or41. 
- apply Or43; by exists l.
- case : c => [ | | | s | c' | l | l | l | c' ]; try (by apply Or44). by apply Or42.
Qed.

Lemma toolmkAnd2_l: forall r,  [ /\ r != CVoid , r != CNot CVoid & (forall l,  r != CAnd l)] -> 
 forall l, mkAnd r (CAnd l) = match undup (merge' [::r] (sort' l)) with
                         | [::] => CNot CVoid
                         | [:: c] => c
                         | s => CAnd s
                         end.
Proof.
case => [ | | | s | c | l | l | l | c ] [] //=.
- move => _ _ h. move/negP: (h l). by case.
- by case :c  => //=.
Qed.

  
Lemma toolmkAnd2_r: forall r, [/\ r != CVoid , r != CNot CVoid & (forall l,  r != CAnd l) ]-> 
 forall l, mkAnd (CAnd l) r = match undup (merge' (sort' l) [::r] ) with
                         | [::] => CNot CVoid
                         | [:: c] => c
                         | s => CAnd s
                         end.
Proof.
case => [ | | | s | c | l | l | l | c ] [] //=.
- move => _ _ h. move/negP: (h l). by case.
- by case :c  => //=.
Qed.

Lemma toolmkAnd3 : forall r1 r2, [/\ r1 != CVoid, r1 != CNot CVoid & (forall l, r1 != CAnd l)] ->
 [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l) ] ->
  mkAnd r1 r2 =  match compare r1 r2 with
     | Lt => CAnd [:: r1; r2]
     | Eq => r1
     | Gt => CAnd [:: r2; r1]
     end
.
Proof.
case => [ | | | s | c | l | l | l | c ] r2 [] _ //=.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- move => _ h. move/negP: (h l); by case.
- case : r2 => [ | | | t | d | k | k | k | d ] _ _ [] //= _.
  move => _ h. move/negP: (h k); by case. by case: d.
- case : r2 => [ | | | t | d | k | k | k | d ] hc1 _ [] //=; try (by case:c hc1).
  move => _ _ h; move/negP : (h k); by case.
  by case: d; case : c hc1.
Qed.

(* end hide *)
(* Proof that the smart constructor is correct *)
Lemma mem_mkAnd : forall r1 r2, mkAnd r1 r2 =i CAnd [:: r1; r2].
Proof.
move => r1 r2. case: (toolmkAnd r1).
- move => heq u; rewrite (eqP heq); clear r1 heq. by rewrite mkAnd_CVoid_lt !CAnd_cons.
- move => heq u; rewrite (eqP heq); clear r1 heq. rewrite mkAnd_CAll_lt. rewrite !CAnd_cons in_CAll.
  by rewrite andbT.
- case => l heq u; rewrite (eqP heq); clear r1 heq. case: (toolmkAnd r2).
  * move => heq; rewrite (eqP heq); clear r2 heq. by rewrite mkAnd_CVoid_rt !CAnd_cons !in_CAnd_nil andbT andbC.
  * move => heq; rewrite (eqP heq); clear r2 heq. rewrite /mkAnd /= !CAnd_cons in_CAll.
    by rewrite !andbT.
  * case => l' heq; rewrite (eqP heq); clear r2 heq. rewrite /mkAnd. 
    by rewrite CAnd_mem_match CAnd_cat !CAnd_cons in_CAnd_nil andbT.
  * case => h1 h2 h3. rewrite toolmkAnd2_r => //. rewrite CAnd_mem_match1.
    by rewrite CAnd_cat !CAnd_cons in_CAnd_nil andbT.
- case => h1 h2 h3. case: (toolmkAnd r2).
  * move => heq u; rewrite (eqP heq); clear r2 heq. by rewrite mkAnd_CVoid_rt /= !CAnd_cons !in_CAnd_nil andbT andbC.
  * move => heq u; rewrite (eqP heq); clear r2 heq.
    rewrite mkAnd_CAll_rt. by rewrite !CAnd_cons in_CAll !andbT.
  * case => l' heq u; rewrite (eqP heq); clear r2 heq. rewrite toolmkAnd2_l => //.
    by rewrite CAnd_mem_match2 CAnd_cat !CAnd_cons !in_CAnd_nil !andbT.
  * case => h'1 h'2 h'3. rewrite toolmkAnd3 => //. case_eq (compare r1 r2) => hc //.
    + rewrite (compare_eq_axiom hc) => u. rewrite !CAnd_cons in_CAnd_nil andbT.
      apply/idP/andP => //=. by case.
    + by move => u; rewrite !CAnd_cons !in_CAnd_nil !andbT andbC.
Qed. 
    

(** Smart constructor for the negation operator *)
Definition mkNot r := match r with 
 | CNot r' => r'
 | _ => CNot r
end.

(* Proof that the negation smart constructor is correct *)
Lemma mem_mkNot : forall r,  mkNot r =i CNot r.
Proof.
(* Note to self: ask Cyril or Georges why apply/starP/negP fails *)
move => r. rewrite /eq_mem. symmetry. move : x.
elim: r  => //= .
- move => c h u. rewrite -!topredE /= /mem_creg /=.
  by rewrite [compl _ u] negbK.
Qed.


(* Other usefull smart constructors in practice, but never used here *)
Definition mkOpt r := mkPlus CEps r.

Definition isEmpty r :=
match r with
| CVoid => true
| _ => false
end.



(** Function that computes the canonical form of a regexp 
   by recursively applying the smart constructors *)

Fixpoint canonize (c:regexp) : canonical_regexp := match c with
 | regexp.Void => CVoid
 | regexp.Eps => CEps
 | regexp.Dot => CDot
 | Atom n => CAtom n
 | Star c' => mkStar (canonize c')
 | Plus c1 c2 => mkPlus (canonize c1) (canonize c2)
 | And c1 c2 => mkAnd (canonize c1) (canonize c2)
 | Conc c1 c2 => mkConc (canonize c1) (canonize c2)
 | Not c1 => mkNot (canonize c1)
end.

(** Proof that the canonize function preserves the language of a regexp *)

Lemma canonize_mem : forall c u, (u \in c) = ( u \in canonize c).
Proof.
elim => [ | | | s | c1 hc1 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1] u //=.
- rewrite -mkStar_mem. rewrite -!topredE /= /mem_creg /=.
  by apply/starP/starP; case => v; move/allP => h1 h2; exists v => //;
  apply/allP => x hx; case/andP : (h1 x hx) => hh1 hh2;
  rewrite !inE hh1 /=; [ rewrite -hc1 | rewrite hc1]. 
- rewrite mem_mkPlus. rewrite -!topredE /= /mem_creg /=. apply/orP/orP.
  * move => [h1 | h2]; [left | right ]; rewrite !inE. by rewrite -hc1. by rewrite orbF -hc2.
  * move => [h1 | h2 ]; [left | right]; rewrite !inE. by rewrite hc1.
    move/orP : h2 => [h1 | h2] //. by rewrite hc2.
- rewrite mem_mkAnd. rewrite -!topredE /= /mem_creg /=. apply/andP/andP; rewrite !inE => [[h1 h2]].
  * by rewrite -hc1 -hc2 h1 h2 andbT.
  * move/andP: h2 => [h2 h3]. by rewrite hc1 h1 hc2 h2.
- rewrite mem_mkConc. rewrite -!topredE /= /mem_creg /=. apply/concP/concP.
  * case => v1 hv1 [v2 hv2 heq]. exists v1. rewrite -hc1 hv1 //. exists v2 => //.
    apply/concP. exists v2. by rewrite -hc2.  by exists nil => //; rewrite cats0.
  * case => v1 hv1 [v2]. case/concP => v2' hv2' [ [|] //= _ ->] ->. 
    exists v1. rewrite hc1 hv1 //. exists v2' => //. by rewrite hc2. by rewrite cats0.
- rewrite mem_mkNot. rewrite -!topredE /= /mem_creg /=. congr negb.
  by rewrite topredE  hc1.
Qed.

(** Two regexp are similar iff there respective canonical forms are Eq *)

Definition similar (c1 c2: regexp) : bool :=
  (canonize c1) == (canonize c2).

(** Two similar regexps recognize the same language *)

Lemma similar_ok : forall c1 c2, similar c1 c2 -> (c1 =i c2).
Proof.
move => c1 c2; rewrite /similar.
move/eqP => h u.
rewrite 2!canonize_mem. by rewrite h.
Qed.

(** mkPlus is symmetric *)
Lemma mkPlusC : forall r1 r2, mkPlus r1 r2 = mkPlus r2 r1.
Proof.
move => r1 r2. case: (toolmkPlus r1).
- by move => heq; rewrite (eqP heq) mkPlus_CVoid_lt mkPlus_CVoid_rt.
- case => l heq; rewrite (eqP heq). case: (toolmkPlus r2).
  + by move => heq2; rewrite (eqP heq2) mkPlus_CVoid_lt mkPlus_CVoid_rt.
  + case => l' heq2; rewrite (eqP heq2) /mkPlus.
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
  + move => h; rewrite toolmkPlus2_r ?toolmkPlus2_l => //.
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
- move => h. case: (toolmkPlus r2).
  + by move => heq; rewrite (eqP heq) mkPlus_CVoid_lt mkPlus_CVoid_rt.
  + case => l heq; rewrite (eqP heq) toolmkPlus2_l ?toolmkPlus2_r => //.
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
  + move => h'. rewrite toolmkPlus3 ?toolmkPlus3 => //.
    rewrite compare_neg. move: (@compare_eq_axiom r2 r1).
    case: (compare r2 r1) => //=.  by move => ->. 
Qed.


(** mkAnd is symmetric *)
Lemma mkAndC : forall r1 r2, mkAnd r1 r2 = mkAnd r2 r1.
Proof.
move => r1 r2. case: (toolmkAnd r1).
- move => heq; by rewrite (eqP heq) mkAnd_CVoid_lt mkAnd_CVoid_rt.
- move => heq; by rewrite (eqP heq) mkAnd_CAll_lt mkAnd_CAll_rt.
- case => l heq; rewrite (eqP heq). case: (toolmkAnd r2).
  + by move => heq2; rewrite (eqP heq2) mkAnd_CVoid_lt mkAnd_CVoid_rt.
  + by move => heq2; rewrite (eqP heq2) mkAnd_CAll_lt mkAnd_CAll_rt.
  + case => l' heq2; rewrite (eqP heq2). rewrite /mkAnd.
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
  + move => h. rewrite toolmkAnd2_r  ?toolmkAnd2_l => //. 
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
- move => h. case: (toolmkAnd r2).
  + by move => heq; rewrite (eqP heq) mkAnd_CVoid_lt mkAnd_CVoid_rt.
  + by move => heq2; rewrite (eqP heq2) mkAnd_CAll_lt mkAnd_CAll_rt.
  + case => l heq; rewrite (eqP heq). rewrite toolmkAnd2_l ?toolmkAnd2_r => //.
    rewrite /merge' merge_sort_sym => //. by apply: leS_trans.
    by apply : leS_antisym. by apply: leS_total.
    apply: sort_sorted. by apply: leS_total.
  + move => h'. rewrite toolmkAnd3 ?toolmkAnd3 => //. 
    rewrite compare_neg. move: (@compare_eq_axiom r2 r1).
    case : (compare r2 r1) => //=. by move => ->. 
Qed.

(** test of wellformedness of canonical regexp. The lists should be: 
   - always longer then two (if empty => absorber,
     if singleton => remove the list)
   - for Plus/And : strictly sorted
*)

Fixpoint wf_re c : bool := match c with
 | CPlus l => [&& (size l >= 2) , uniq l , sorted cregexp_le l & all wf_re l]
 | CAnd l => [&& (size l >= 2) , uniq l , sorted cregexp_le l &  all wf_re l]
 | CConc l => (size l >= 2)  && all wf_re l 
 | CStar c => wf_re c
 | CNot c => match c with
      | CNot _ => false
      | _ => wf_re c
      end
 | _ => true
end.

(* begin hide *)
(* helper rewriting lemmas *)
Lemma wf_re_CPlus: forall l, wf_re (CPlus l) = [&& (size l >= 2) , uniq l , sorted cregexp_le l & all wf_re l].
by move => l.
Qed.

Lemma wf_re_CAnd: forall l, wf_re (CAnd l) = [&& (size l >= 2) , uniq l , sorted cregexp_le l & all wf_re l].
by move => l.
Qed.


Lemma mkPlus_unfold: forall l1 l2, wf_re (CPlus l1) -> wf_re (CPlus l2) -> 
  mkPlus (CPlus l1) (CPlus l2) = CPlus (undup (merge' (sort' l1) (sort' l2))).
Proof.
move => l1 l2; rewrite !wf_re_CPlus /mkPlus. case/and4P => hs1 hu1 hst1 ha1.
case/and4P => hs2 hu2 hst2 ha2 /=.
have : (2 <= size (undup (merge' (sort' l1) (sort' l2)))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) (sort' l2))) (undup (l1++l2))).
  apply (@leq_trans (size l2)). done. rewrite -{1}(@undup_id  _ l2). apply tool_undup_size. 
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq.
  move => u. by rewrite !mem_undup mem_merge !mem_cat !mem_sort.
clear hu1 hu2 hst2 hst2 ha1 ha2. case: (undup (merge' (sort' l1) (sort' l2))) => //.
move => hd. by case => //=.
Qed.

Lemma mkPlus_unfold2: forall l1 r2, wf_re (CPlus l1) -> wf_re r2 -> 
  (r2 != CVoid /\ (forall l, r2 != CPlus l)) ->
  mkPlus (CPlus l1) r2 = CPlus (undup (merge' (sort' l1) [::r2])). 
Proof.
move => l1 r2; rewrite !wf_re_CPlus. case/and4P => hs1 hu1 hst1 ha1.
move => hw2 hh.
have : (2 <= size (undup (merge' (sort' l1) [::r2]))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) [::r2])) (undup (l1++[::r2]))).
  apply (@leq_trans (size l1)). done. rewrite -{1}(@undup_id _ l1). apply tool_undup_size2. 
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq.
  move => u. by rewrite !mem_undup mem_merge !mem_cat !mem_sort.
rewrite toolmkPlus2_r => //. clear hu1 hs1 hst1 ha1.
case: (undup (merge' (sort' l1) [::r2])) => //.
move => hd. by case => //=.
Qed.

Lemma mkPlus_unfold3: forall l1 r2, wf_re (CPlus l1) -> wf_re r2 -> 
  (r2 != CVoid /\ (forall l, r2 != CPlus l) ) ->
  mkPlus r2 (CPlus l1) = CPlus (undup (merge' [::r2] (sort' l1) )).
Proof.
move => l1 r2 h1 h2 h3. rewrite mkPlusC. rewrite /merge' merge_sort_sym =>//.
by apply: mkPlus_unfold2. by apply: leS_trans. by apply: leS_antisym.
by apply: leS_total. apply: sort_sorted. by apply: leS_total.
Qed.

Lemma mkAnd_unfold: forall l1 l2, wf_re (CAnd l1) -> wf_re (CAnd l2) -> 
  mkAnd (CAnd l1) (CAnd l2) = CAnd (undup (merge' (sort' l1) (sort' l2))).
Proof.
move => l1 l2; rewrite !wf_re_CAnd. case/and4P => hs1 hu1 hst1 ha1.
case/and4P => hs2 hu2 hst2 ha2 /=.
have : (2 <= size (undup (merge' (sort' l1) (sort' l2)))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) (sort' l2))) (undup (l1++l2))).
  apply (@leq_trans (size l2)). done. rewrite -{1}(@undup_id  _ l2). apply tool_undup_size. 
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq.
  move => u. by rewrite !mem_undup mem_merge !mem_cat !mem_sort.
clear hu1 hu2 hst2 hst2 ha1 ha2. rewrite /mkAnd. case: (undup (merge' (sort' l1) (sort' l2))) => //.
move => hd. by case => //=.
Qed.

Lemma mkAnd_unfold2: forall l1 r2, wf_re (CAnd l1) -> wf_re r2 -> 
  [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l) ] -> 
  mkAnd (CAnd l1) r2 = CAnd (undup (merge' (sort' l1) [::r2])). 
Proof.
move => l1 r2; rewrite !wf_re_CAnd. case/and4P => hs1 hu1 hst1 ha1.
move => hw2 hh.
have : (2 <= size (undup (merge' (sort' l1) [::r2]))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) [::r2])) (undup (l1++[::r2]))).
  apply (@leq_trans (size l1)). done. rewrite -{1}(@undup_id _ l1). apply tool_undup_size2. 
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq.
  move => u. by rewrite !mem_undup mem_merge !mem_cat !mem_sort.
rewrite toolmkAnd2_r  => //. clear hu1 hs1 hst1 ha1.
case: (undup (merge' (sort' l1) [::r2])) => //.
move => hd. by case => //=.
Qed.

Lemma mkAnd_unfold3: forall l1 r2, wf_re (CAnd l1) -> wf_re r2 -> 
  [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l)] ->
  mkAnd r2 (CAnd l1) = CAnd (undup (merge' [::r2] (sort' l1) )).
Proof.
move => l1 r2 h1 h2 h3. rewrite mkAndC. rewrite /merge' merge_sort_sym =>//.
by apply: mkAnd_unfold2. by apply: leS_trans. by apply: leS_antisym.
by apply: leS_total. apply: sort_sorted. by apply: leS_total.
Qed.

(* Note to self: the following proofs should be simplified *)
Lemma wf_CPlus_plus_plus: forall l1 l2, wf_re (CPlus l1) -> wf_re (CPlus l2) ->
  wf_re (mkPlus (CPlus l1) (CPlus l2)).
Proof.
rewrite /mkPlus => l1 l2 /=.  case/and4P => hs1 hu1 hst1.
move/allP => ha1. case/and4P => hs2 hu2 hst2. move/allP => ha2.
case_eq (undup (merge' (sort' l1) (sort' l2))) => //.
move => hd. case => [ | hd2 tl] //=. move => heq. have : hd \in l1 ++ l2.
rewrite mem_cat. rewrite -(@mem_sort _ cregexp_le l1). rewrite -(@mem_sort _ cregexp_le l2).
rewrite -mem_cat. rewrite -(@mem_merge _ cregexp_le). rewrite -mem_undup. rewrite heq. 
by apply/orP; left. rewrite mem_cat. case/orP => hu. by apply: ha1. by apply : ha2.
move => heq. have : [&& (hd \in l1 ++ l2) , (hd2 \in l1 ++ l2) & (all (fun a => a \in l1 ++ l2) tl )].
  apply/and3P; split.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; by left.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. apply/orP ; by left. 
  apply/allP. move => x hx. 
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. by apply/orP; right.
case/and3P => hh1 hh2. move/allP => hh3.  apply/and3P ; split.
have : uniq [:: hd , hd2 & tl]. rewrite -heq. by rewrite undup_uniq. move => hu.  apply/and3P; split.
by case/and3P : hu. by case/and3P: hu. by case/and3P: hu.
have: sorted cregexp_le [:: hd, hd2 & tl]. rewrite -heq. rewrite sorted_undup => //.
by apply: leS_trans. apply merge_sorted. by apply leS_total. apply: sort_sorted. by apply leS_total.
apply: sort_sorted. by apply leS_total. move => hs. 
apply/andP; split. by case/andP: hs. by case/andP: hs. 
apply/and3P; split. rewrite mem_cat in hh1.
case/orP : hh1 => hh1. by apply: ha1. by apply: ha2. rewrite mem_cat in hh2.
case/orP : hh2 => hh2. by apply: ha1. by apply: ha2. apply/allP => x hx. 
have := (hh3 x hx). rewrite mem_cat. case/orP => hu. by apply: ha1. by apply: ha2.
Qed.

Lemma wf_CAnd_and_and: forall l1 l2, wf_re (CAnd l1) -> wf_re (CAnd l2) ->
  wf_re (mkAnd (CAnd l1) (CAnd l2)).
Proof.
move => l1 l2 /=. case/and4P => hs1 hu1 hst1.
move/allP => ha1. case/and4P => hs2 hu2 hst2. move/allP => ha2.
rewrite /mkAnd. case_eq (undup (merge' (sort' l1) (sort' l2))) => //.
move => hd. case => [ | hd2 tl] //=. move => heq. have : hd \in l1 ++ l2.
rewrite mem_cat. rewrite -(@mem_sort _ cregexp_le l1). rewrite -(@mem_sort _ cregexp_le l2).
rewrite -mem_cat. rewrite -(@mem_merge _ cregexp_le). rewrite -mem_undup. rewrite heq. 
by apply/orP; left. rewrite mem_cat. case/orP => hu. by apply: ha1. by apply : ha2.
move => heq. have : (hd \in l1 ++ l2) && (hd2 \in l1 ++ l2) && (all (fun a => a \in l1 ++ l2) tl).
  apply/andP; split. apply/andP; split.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; by left.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. apply/orP ; by left. 
  apply/allP. move => x hx. 
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le l2).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. by apply/orP; right.
case/andP. case/andP => hh1 hh2. move/allP => hh3.  apply/andP; split.
have : uniq [:: hd , hd2 & tl]. rewrite -heq. by rewrite undup_uniq. case/andP => hu. case/andP => hu' htl.
apply/andP; split => //.  by apply/andP; split.
have: sorted cregexp_le [:: hd, hd2 & tl]. rewrite -heq. rewrite sorted_undup => //.
by apply: leS_trans. apply merge_sorted. by apply leS_total. apply: sort_sorted. by apply leS_total.
apply: sort_sorted. by apply leS_total. case/andP => hss1 hss2.
apply/andP; split. by apply/andP; split. apply/andP; split.  rewrite mem_cat in hh1.
case/orP : hh1 => hh1. by apply: ha1. by apply: ha2. apply/andP; split. rewrite mem_cat in hh2.
case/orP : hh2 => hh2. by apply: ha1. by apply: ha2. apply/allP => x hx. 
have := (hh3 x hx). rewrite mem_cat. case/orP => hu. by apply: ha1. by apply: ha2.
Qed.

Lemma wf_CPlus_plus_nplus: forall l1 r2, wf_re (CPlus l1) -> wf_re r2 -> 
  (r2 != CVoid /\ (forall l, r2 != CPlus l)) -> wf_re (mkPlus (CPlus l1) r2).
Proof.
move => l1 r2. rewrite wf_re_CPlus. case/and4P => h1 h2 h3. move/allP => h4 h hh.
rewrite toolmkPlus2_r => //.  case_eq (undup (merge' (sort' l1) [:: r2])) => //. 
move => hd. case => [ | hd2 tl] //=. move => heq. have : hd \in l1 ++ [:: r2].
rewrite mem_cat. rewrite -(@mem_sort _ cregexp_le l1). rewrite -(@mem_sort _ cregexp_le [:: r2]).
rewrite -mem_cat. rewrite -(@mem_merge _ cregexp_le). rewrite -mem_undup. rewrite heq. 
by apply/orP; left. rewrite mem_cat. case/orP => hu. by apply: h4. rewrite mem_seq1 in hu. by  rewrite (eqP hu).
move => heq. have : (hd \in l1 ++ [:: r2]) && (hd2 \in l1 ++ [::r2]) && (all (fun a => a \in l1 ++ [::r2]) tl).
  apply/andP; split. apply/andP; split.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; by left.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. apply/orP ; by left. 
  apply/allP. move => x hx. 
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. by apply/orP; right.
case/andP. case/andP => hh3 hh4. move/allP => hh5.  apply/andP; split.
have : uniq [:: hd , hd2 & tl]. rewrite -heq. by rewrite undup_uniq. done.  apply/andP; split.
have : sorted cregexp_le [:: hd, hd2 & tl]. rewrite -heq. rewrite sorted_undup => //.
by apply: leS_trans. apply merge_sorted. by apply leS_total. apply: sort_sorted. by apply leS_total.
done. case/andP => hss1 hss2.
by apply/andP; split. apply/andP; split. rewrite mem_cat in hh3. case/orP : hh3 => hh3. by apply: h4.
rewrite mem_seq1 in hh3. by rewrite (eqP hh3). apply/andP; split.
rewrite mem_cat in hh4. case/orP : hh4 => hh4. by apply: h4.
rewrite mem_seq1 in hh4. by rewrite (eqP hh4).
apply/allP => x hx. 
have := (hh5 x hx). rewrite mem_cat. case/orP => hu. by apply: h4.
by rewrite mem_seq1 in hu; rewrite (eqP hu).
Qed.

Lemma wf_CAnd_and_nand: forall l1 r2, wf_re (CAnd l1) -> wf_re r2 -> 
  [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l) ] ->
   wf_re (mkAnd (CAnd l1) r2).
Proof.
move => l1 r2. rewrite wf_re_CAnd. case/and4P => h1 h2 h3. move/allP => h4 h hh.
rewrite toolmkAnd2_r => //.  case_eq (undup (merge' (sort' l1) [:: r2])) => //. 
move => hd. case => [ | hd2 tl] //=. move => heq. have : hd \in l1 ++ [:: r2].
rewrite mem_cat. rewrite -(@mem_sort _ cregexp_le l1). rewrite -(@mem_sort _ cregexp_le [:: r2]).
rewrite -mem_cat. rewrite -(@mem_merge _ cregexp_le). rewrite -mem_undup. rewrite heq. 
by apply/orP; left. rewrite mem_cat. case/orP => hu. by apply: h4. rewrite mem_seq1 in hu. by  rewrite (eqP hu).
move => heq. have : (hd \in l1 ++ [:: r2]) && (hd2 \in l1 ++ [::r2]) && (all (fun a => a \in l1 ++ [::r2]) tl).
  apply/andP; split. apply/andP; split.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; by left.
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. apply/orP ; by left. 
  apply/allP. move => x hx. 
  rewrite mem_cat -(@mem_sort _ cregexp_le l1)  -(@mem_sort _ cregexp_le [::r2]).
  rewrite -mem_cat -(@mem_merge _ cregexp_le) -mem_undup heq. apply/orP; right. by apply/orP; right.
case/andP. case/andP => hh4 hh5. move/allP => hh6.  apply/andP; split.
have : uniq [:: hd , hd2 & tl]. rewrite -heq. by rewrite undup_uniq. done. 
apply/andP; split.
have : sorted cregexp_le [:: hd, hd2 & tl]. rewrite -heq. rewrite sorted_undup => //.
by apply: leS_trans. apply merge_sorted. by apply leS_total. apply: sort_sorted. by apply leS_total.
done. case/andP => hss1 hss2.
by apply/andP; split.
apply/andP; split. rewrite mem_cat in hh4. case/orP : hh4 => hh4. by apply: h4.
rewrite mem_seq1 in hh4. by rewrite (eqP hh4). apply/andP; split.
rewrite mem_cat in hh5. case/orP : hh5 => hh5. by apply: h4.
rewrite mem_seq1 in hh5. by rewrite (eqP hh5).
apply/allP => x hx. 
have := (hh6 x hx). rewrite mem_cat. case/orP => hu. by apply: h4.
by rewrite mem_seq1 in hu; rewrite (eqP hu).
Qed.


Lemma wf_CPlus_nplus_nplus : forall r1 r2, wf_re r1 -> wf_re r2 ->
 (r1 != CVoid /\ (forall l, r1 != CPlus l)) ->
 (r2 != CVoid /\ (forall l, r2 != CPlus l)) ->
  wf_re (mkPlus r1 r2).
Proof.
move => r1 r2 hw1 hw2 hh1 hh2.
rewrite toolmkPlus3 => //. case_eq (compare r1 r2) => heq //=.
- apply/andP; split => //. rewrite andbT. 
  apply/negP. rewrite mem_seq1 => heq2. 
  by rewrite (eqP heq2) compare_refl in heq.
  apply/andP; split. rewrite andbT. 
  by rewrite /cregexp_le /leS /cmpS /= heq. 
  by rewrite hw1 hw2. 
- apply/andP; split. rewrite andbT. 
  apply/negP. rewrite mem_seq1 => heq2. 
  by rewrite (eqP heq2) compare_refl in heq.
  move : heq. rewrite compare_neg /cregexp_le /leS /cmpS /=. 
  case: (compare r2 r1) => //=. by rewrite hw1 hw2.
Qed.


Lemma wf_CAnd_nand_nand : forall r1 r2, wf_re r1 -> wf_re r2 ->
 [/\ r1 != CVoid , r1 != CNot CVoid & (forall l, r1 != CAnd l)] ->
 [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l)] ->
  wf_re (mkAnd r1 r2).
Proof.
move => r1 r2 hw1 hw2 hh1 hh2.
rewrite toolmkAnd3 /mkAnd => //. case_eq (compare r1 r2) => heq //=.
- apply/andP; split. rewrite andbT. apply/negP. rewrite mem_seq1 => heq2.
  by rewrite (eqP heq2) compare_refl in heq. apply/andP; split. 
  rewrite andbT.
  by rewrite /cregexp_le /leS /cmpS /= heq. by rewrite hw1 hw2.
- apply/andP; split. rewrite andbT. apply/negP. 
  rewrite mem_seq1 => heq2. by rewrite (eqP heq2) compare_refl in heq.
  apply/andP; split. rewrite andbT. move : heq.
  rewrite compare_neg /cregexp_le /leS /cmpS /=.
  case: (compare r2 r1) => //=. by rewrite hw1 hw2.
Qed.


(* mkPlus preserves the wellformedness of expression *)
Lemma wf_CPlus : forall r1 r2, wf_re r1 -> wf_re r2 -> wf_re (mkPlus r1 r2).
Proof.
move => r1 r2. case: (toolmkPlus r1).
- move => heq; rewrite (eqP heq); clear heq r1. by rewrite mkPlus_CVoid_lt.
- case => l1 heq; rewrite (eqP heq); clear heq r1. case : (toolmkPlus r2).
  * move => heq; rewrite (eqP heq); clear heq r2. by rewrite mkPlus_CVoid_rt.
  * case => l2 heq; rewrite (eqP heq)  ; clear heq r2.
    move => h1 h2. by apply wf_CPlus_plus_plus.
  * move => h hw1 hw2; by apply wf_CPlus_plus_nplus.
- move => hh1 hw1. case: (toolmkPlus r2).
  * move => heq; rewrite (eqP heq). move => _. by rewrite mkPlus_CVoid_rt.
  * case => l heq. rewrite (eqP heq); clear heq. move => h2.
    rewrite mkPlusC. by apply wf_CPlus_plus_nplus.
  * move => hh2 hw2. by apply wf_CPlus_nplus_nplus.
Qed.


(* mkAnd preserves the wellformedness of expression *)
Lemma wf_CAnd : forall r1 r2, wf_re r1 -> wf_re r2 -> wf_re (mkAnd r1 r2).
Proof.
move => r1 r2. case: (toolmkAnd r1).
- move => heq; rewrite (eqP heq); clear heq r1. by rewrite mkAnd_CVoid_lt.
- move => heq; rewrite (eqP heq); clear heq r1. by rewrite mkAnd_CAll_lt.
- case => l1 heq; rewrite (eqP heq); clear heq r1. case : (toolmkAnd r2).
  * move => heq; rewrite (eqP heq); clear heq r2. by rewrite mkAnd_CVoid_rt.
  * move => heq; rewrite (eqP heq); clear heq r2. by rewrite mkAnd_CAll_rt.
  * case => l2 heq; rewrite (eqP heq)  ; clear heq r2.
    move => h1 h2. by apply wf_CAnd_and_and.
  * move => hh1 hw1 hw2. by apply wf_CAnd_and_nand.
- move => hh1 hw1. case: (toolmkAnd r2).
  * move => heq; rewrite (eqP heq). move => _. by rewrite mkAnd_CVoid_rt.
  * move => heq; rewrite (eqP heq); clear heq r2. by rewrite mkAnd_CAll_rt.
  * case => l heq. rewrite (eqP heq); clear heq. move => hw2.
    rewrite mkAndC. by apply wf_CAnd_and_nand.
  * move => hh2 hw2. by apply wf_CAnd_nand_nand.
Qed.
(* end hide *)

(** mkPlus get rid of duplicates (requires wf) *)

Lemma mkPlus_id : forall r, wf_re r -> mkPlus r r = r.
Proof.
case => [ | | | s | c | l | l | l | c ] //=; try(
  by rewrite /mkPlus compare_refl).
move => h. rewrite mkPlus_unfold => //. f_equal.
apply : (@sorted_eq _ cregexp_le). by apply: leS_trans.
by apply: leS_antisym. apply: sorted_undup.
by apply: leS_trans. apply: merge_sorted. by apply: leS_total.
apply : sort_sorted. by apply : leS_total.
apply: sort_sorted. by apply: leS_total.
by case/and4P: h.
apply: uniq_perm. apply undup_uniq. by case/and4P: h.
move => u. rewrite mem_undup mem_merge mem_cat !mem_sort.
by apply/orP/idP; [case | left].
Qed.

(** mkAnd get rid of duplicates (requires wf) *)

Lemma mkAnd_id : forall r, wf_re r -> mkAnd r r = r.
Proof.
case => [ | | | s | c | l | l | l | c ] //=; try (
   by rewrite /mkAnd compare_refl).
- move => h. rewrite mkAnd_unfold => //. f_equal.
  apply : (@sorted_eq _ cregexp_le). by apply: leS_trans.
  by apply: leS_antisym. apply: sorted_undup.
  by apply: leS_trans. apply: merge_sorted. by apply: leS_total.
  apply : sort_sorted. by apply : leS_total.
  apply: sort_sorted. by apply: leS_total.
  by case/and4P: h.
  apply: uniq_perm. apply undup_uniq. by case/and4P: h.
  move => u. rewrite mem_undup mem_merge mem_cat !mem_sort.
  by apply/orP/idP; [case | left].
- case: c => [ | | | s | c' | l | l | l | c' ] //= ; 
    by rewrite toolmkAnd3 // compare_refl.
Qed.

Lemma mkStar_id : forall r, wf_re r -> mkStar (mkStar r) = mkStar r.
Proof.
by case. 
Qed.

Lemma mkNot_id : forall r , wf_re r -> 
  mkNot (mkNot r) == r. 
Proof.
case => //=. by case. 
Qed.

(* begin hide *)

Lemma wf_CConc : forall r1 r2, wf_re r1 -> wf_re r2 -> wf_re (mkConc r1 r2).
Proof.
move => r1. case: (toolmkConc r1).
- by move => heq r2; rewrite (eqP heq) mkConc_CVoid_lt.
- by move => heq r2; rewrite (eqP heq) mkConc_CEps_lt.
- case => l heq r2; rewrite (eqP heq) /=;clear heq r1. case/andP => h1 h2. case: (toolmkConc r2).
  * by move => heq; rewrite (eqP heq).
  * move => heq _; rewrite (eqP heq). by apply/andP; split.
  * case => l' heq; rewrite (eqP heq) /=; clear heq r2.
    case/andP => h3 h4. apply/andP; split. rewrite size_cat /=.
    by apply ltn_addl.  by rewrite all_cat h2 h4.
  * case. case: r2 => [ | | | t | d | k | k | k | d ] //=. 
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat /= andbT.
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat andbT.
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat h2 /= andbT.
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat h2 /= andbT.
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat h2 /= andbT.
    + move => _ _ h. move/negP : (h k); by case.
    + move => _ _ _ hr2. apply/andP; split.
      rewrite size_cat /=; change 1 with (0+1); rewrite ltn_add2r; by apply (@ltn_trans 1).
      by rewrite all_cat h2 /= andbT.
- move => hr1 r2 hw1. case: (toolmkConc r2).
  * by move => heq; rewrite (eqP heq) mkConc_CVoid_rt.
  * by move => heq; rewrite (eqP heq) mkConc_CEps_rt.
  * case => l heq; rewrite (eqP heq) /=; clear r2 heq.
    case/andP => h1 h2. rewrite mkConc_unfold2 => //=.
    rewrite h2 hw1 !andbT. by apply (@ltn_trans (size l)).
  * move => hr2 hw2. rewrite mkConc_unfold3 => //=. by rewrite hw1 hw2.
Qed.

Lemma wf_CStar : forall c, wf_re c -> wf_re (mkStar c).
Proof.
case => //=.
Qed.

Lemma wf_CNot : forall c, wf_re c -> wf_re (mkNot c).
Proof.
case => //=.
by case.
Qed.

(* end hide*)

(** Every canonical regexp is wf *)

Lemma wf_re_can : forall c, wf_re (canonize c).
Proof.
elim => [ | | | s | c | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c ] //=.
- by apply wf_CStar.
- by apply wf_CPlus.
- by apply wf_CAnd.
- by apply wf_CConc. 
- by apply wf_CNot.
Qed. 



(* begin hide *)
(* helper package again *)
Lemma mkPlusAC_plus_plus_plus: forall l1 l2 l3, wf_re (CPlus l1) ->
 wf_re (CPlus l2) -> wf_re (CPlus l3) ->
 mkPlus (mkPlus (CPlus l1) (CPlus l2)) (CPlus l3) = mkPlus (mkPlus (CPlus l1) (CPlus l3)) (CPlus l2).
Proof.
move => l1 l2 l3 hw1 hw2 hw3.
rewrite !mkPlus_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
by apply leS_trans. by apply leS_antisym.
apply : sorted_undup. by apply leS_trans. apply : merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply : sorted_undup. by apply leS_trans. apply : merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort.
by rewrite orbAC. rewrite -mkPlus_unfold => //. by apply wf_CPlus. rewrite -mkPlus_unfold => //. by apply wf_CPlus.
Qed.

Lemma mkAndAC_and_and_and: forall l1 l2 l3, wf_re (CAnd l1) ->
 wf_re (CAnd l2) -> wf_re (CAnd l3) ->
 mkAnd (mkAnd (CAnd l1) (CAnd l2)) (CAnd l3) = mkAnd (mkAnd (CAnd l1) (CAnd l3)) (CAnd l2).
Proof.
move => l1 l2 l3 hw1 hw2 hw3.
rewrite !mkAnd_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
by apply leS_trans. by apply leS_antisym.
apply : sorted_undup. by apply leS_trans. apply : merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply : sorted_undup. by apply leS_trans. apply : merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort.
by rewrite orbAC. rewrite -mkAnd_unfold => //. by apply wf_CAnd. rewrite -mkAnd_unfold => //. by apply wf_CAnd.
Qed.


Lemma mkPlusAC_plus_plus_nplus: forall l1 l2 r3, wf_re (CPlus l1) ->
  wf_re (CPlus l2) -> wf_re r3 -> 
  (r3 != CVoid /\ (forall l, r3 != CPlus l)) ->
  mkPlus (mkPlus (CPlus l1) (CPlus l2)) r3 = mkPlus (mkPlus (CPlus l1) r3) (CPlus l2).
Proof.
move => l1 l2 r3 hw1 hw2 hw3 hh.
rewrite mkPlus_unfold => //. rewrite !toolmkPlus2_r => //.
have hs1 : 2 <= size (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3])).
  rewrite (@perm_size _ (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [::r3])) (undup (l1++l2++[::r3]))).
  rewrite wf_re_CPlus in hw1. case/and4P : hw1 => h1 h2 h3 _.
  apply (@leq_trans (size l1)).  done. rewrite -{1}(@undup_id _ l1). by apply tool_undup_size2.
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
  by rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort orbA.
have hs2 : (2 <= size (undup (merge' (sort' l1) [::r3]))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) [::r3])) (undup (l1++[::r3]))).
  rewrite wf_re_CPlus in hw1. case/and4P : hw1 => h1 h2 h3 _.
  apply (@leq_trans (size l1)).  done. rewrite -{1}(@undup_id _ l1). by apply tool_undup_size2.
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
  by rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
replace (match undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3]) with
  | [::] => CVoid
  | [:: c] => c
  | [:: c, s1 & s2] => CPlus [:: c, s1 & s2]
end) with (CPlus (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3]))).
replace (match undup (merge' (sort' l1) [:: r3]) with
  | [::] => CVoid
  | [:: c] => c
  | [:: c, s1 & s2] => CPlus [:: c, s1 & s2]
end) with (CPlus (undup (merge' (sort' l1) [::r3]))).
rewrite mkPlus_unfold. f_equal.
apply (@sorted_eq _ cregexp_le). by apply leS_trans. by apply leS_antisym.
apply sorted_undup. by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. done. 
apply sorted_undup. by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
by rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort orbAC.
rewrite wf_re_CPlus. apply/and4P; split. done. by apply undup_uniq. rewrite  sorted_undup => //.
by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. done. move :hw1. rewrite wf_re_CPlus.
case/and4P => _  _ _. move/allP => hall. apply/allP => x. rewrite mem_undup mem_merge mem_cat !mem_sort.
case/orP. by move => hu; apply: hall. rewrite mem_seq1 => heq. by rewrite (eqP heq). done.
move : hs2. case: (undup (merge' (sort' l1) [::r3])) => //. move => hd. by case.
move : hs1. case: (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [::r3])) => // hd.
by case.
Qed.

Lemma mkAndAC_and_and_nand: forall l1 l2 r3, wf_re (CAnd l1) ->
  wf_re (CAnd l2) -> wf_re r3 -> 
  [/\ r3 != CVoid , r3 != CNot CVoid & (forall l, r3 != CAnd l)] ->
  mkAnd (mkAnd (CAnd l1) (CAnd l2)) r3 = mkAnd (mkAnd (CAnd l1) r3) (CAnd l2).
Proof.
move => l1 l2 r3 hw1 hw2 hw3 hh.
rewrite mkAnd_unfold => //. rewrite !toolmkAnd2_r => //.
have hs1 : 2 <= size (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3])).
  rewrite (@perm_size _ (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [::r3])) (undup (l1++l2++[::r3]))).
  rewrite wf_re_CAnd in hw1. case/and4P : hw1 => h1 h2 h3 _.
  apply (@leq_trans (size l1)).  done. rewrite -{1}(@undup_id _ l1). by apply tool_undup_size2.
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
  by rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort orbA.
have hs2 : (2 <= size (undup (merge' (sort' l1) [::r3]))).
  rewrite (@perm_size _ (undup (merge' (sort' l1) [::r3])) (undup (l1++[::r3]))).
  rewrite wf_re_CAnd in hw1. case/and4P : hw1 => h1 h2 h3 _.
  apply (@leq_trans (size l1)).  done. rewrite -{1}(@undup_id _ l1). by apply tool_undup_size2.
  done. apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
  by rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
replace (match undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3]) with
  | [::] => CNot CVoid
  | [:: c] => c
  | [:: c, s1 & s2] => CAnd [:: c, s1 & s2]
end) with (CAnd (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [:: r3]))).
replace (match undup (merge' (sort' l1) [:: r3]) with
  | [::] => CNot CVoid
  | [:: c] => c
  | [:: c, s1 & s2] => CAnd [:: c, s1 & s2]
end) with (CAnd (undup (merge' (sort' l1) [::r3]))).
rewrite mkAnd_unfold. f_equal.
apply (@sorted_eq _ cregexp_le). by apply leS_trans. by apply leS_antisym.
apply sorted_undup. by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. done. 
apply sorted_undup. by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. apply sort_sorted. by apply leS_total.
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
by rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_undup !mem_merge !mem_cat !mem_sort orbAC.
rewrite wf_re_CAnd. apply/and4P; split. 
done. by apply undup_uniq. rewrite  sorted_undup => //.
by apply leS_trans. apply merge_sorted. by apply leS_total.
apply sort_sorted. by apply leS_total. done. move :hw1. rewrite wf_re_CAnd.
case/and4P => _ _ _. move/allP => hall. apply/allP => x. rewrite mem_undup mem_merge mem_cat !mem_sort.
case/orP. by move => hu; apply: hall. rewrite mem_seq1 => heq. by rewrite (eqP heq). done.
move : hs2. case: (undup (merge' (sort' l1) [::r3])) => //. move => hd. by case.
move : hs1. case: (undup (merge' (sort' (undup (merge' (sort' l1) (sort' l2)))) [::r3])) => // hd.
by case.
Qed.

Lemma mkPlusAC_nplus_nplus_plus : forall r1 r2 l3, wf_re r1 -> wf_re r2 -> wf_re (CPlus l3) ->
 (r1 != CVoid /\ (forall l, r1 != CPlus l)) ->
 (r2 != CVoid /\ (forall l, r2 != CPlus l)) ->
mkPlus (mkPlus r1 r2) (CPlus l3) = mkPlus (mkPlus r1 (CPlus l3)) r2.
Proof.
move => r1 r2 l3 hw1 hw2 hw3 hh1 hh2.
rewrite (@toolmkPlus3 r1 r2) => //. rewrite (@mkPlus_unfold3 _ r1) => //.
rewrite (@mkPlus_unfold2 _ r2) => //.
case_eq (compare r1 r2) => heq.
- rewrite mkPlus_unfold3 => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted. by apply leS_total.
  done. apply sort_sorted. by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted. 
  by apply leS_total.
  apply sort_sorted. by apply leS_total. done. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  rewrite (compare_eq_axiom heq). by rewrite orbAC orbb.
- rewrite mkPlus_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted. by apply leS_total.
  apply sort_sorted. by apply leS_total. apply sort_sorted. 
  by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted. 
  by apply leS_total.
  apply sort_sorted. by apply leS_total. done. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_seq2 mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  by rewrite orbAC. rewrite wf_re_CPlus /=. apply/and4P; split => //. 
  rewrite andbT.
  apply/negP; rewrite mem_seq1 => heq2. move :heq.
  rewrite (eqP heq2). by rewrite compare_refl.
  by rewrite andbT /cregexp_le /leS /cmpS /= heq.
  by rewrite hw2.
- rewrite mkPlus_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted. by apply leS_total.
  apply sort_sorted. by apply leS_total. apply sort_sorted. 
  by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted. 
  by apply leS_total.
  apply sort_sorted. by apply leS_total. done. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_seq2 mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  by rewrite orbAC orbC orbA orbAC. 
  rewrite wf_re_CPlus /=. apply/and4P; split.
  rewrite andbT. apply/negP; rewrite mem_seq1 => heq2. move :heq.
  rewrite (eqP heq2). by rewrite compare_refl.
  rewrite andbT. move : heq ; rewrite /cregexp_le /leS /cmpS /= compare_neg.
  by case_eq (compare r2 r1).  by rewrite hw2. by rewrite andbT.
move: hw3. rewrite !wf_re_CPlus. case/and4P => h3 h4 h5. move/allP => h6.
apply/and4P; split. 
apply (@leq_trans (size l3)) => //. 
rewrite (@perm_size _ (undup (merge' [::r1] (sort' l3))) 
                         (undup ([::r1]++l3))).
rewrite -{1}(@undup_id _ l3) => //. by apply tool_undup_size. 
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
by rewrite !mem_undup mem_merge !mem_cat mem_sort !mem_seq1.
by apply undup_uniq. apply sorted_undup. by apply leS_trans.
apply merge_sorted =>// . by apply leS_total. apply sort_sorted.
by apply leS_total. apply/allP => x.
rewrite mem_undup mem_merge mem_cat mem_sort mem_seq1.
case/orP => hu. by rewrite (eqP hu).  by apply : h6.
Qed.

Lemma mkAndAC_nand_nand_and : forall r1 r2 l3, wf_re r1 -> wf_re r2 -> wf_re (CAnd l3) ->
 [/\ r1 != CVoid , r1 != CNot CVoid & (forall l, r1 != CAnd l)] ->
 [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l)] ->
mkAnd (mkAnd r1 r2) (CAnd l3) = mkAnd (mkAnd r1 (CAnd l3)) r2.
Proof.
move => r1 r2 l3 hw1 hw2 hw3 hh1 hh2.
rewrite (@toolmkAnd3 r1 r2) => //. rewrite (@mkAnd_unfold3 _ r1) => //.
rewrite (@mkAnd_unfold2 _ r2) => //.
case_eq (compare r1 r2) => heq.
- rewrite mkAnd_unfold3 => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted => //. by apply leS_total.
  apply sort_sorted. by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted =>//.
  by apply leS_total.
  apply sort_sorted. by apply leS_total. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  rewrite (compare_eq_axiom heq). by rewrite orbAC orbb.
- rewrite mkAnd_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted. by apply leS_total.
  apply sort_sorted. by apply leS_total. apply sort_sorted. 
  by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted. 
  by apply leS_total.
  apply sort_sorted. by apply leS_total. done. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_seq2 mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  by rewrite orbAC. rewrite wf_re_CAnd /=. apply/and4P; split.
  rewrite andbT. apply/negP; rewrite mem_seq1 => heq2. move :heq.
  rewrite (eqP heq2). by rewrite compare_refl.
  rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq.
  by rewrite hw1. by rewrite andbT.
- rewrite mkAnd_unfold => //. f_equal. apply (@sorted_eq _ cregexp_le).
  by apply leS_trans. by apply leS_antisym. apply sorted_undup.
  by apply leS_trans. apply merge_sorted. by apply leS_total.
  apply sort_sorted. by apply leS_total. apply sort_sorted. 
  by apply leS_total.
  apply sorted_undup. by apply leS_trans. apply merge_sorted. 
  by apply leS_total.
  apply sort_sorted. by apply leS_total. done. apply uniq_perm.
  by apply undup_uniq. by apply undup_uniq. move => u.
  rewrite !mem_undup !mem_merge !mem_cat !mem_sort.
  rewrite mem_seq2 mem_undup mem_merge mem_cat !mem_sort !mem_seq1.
  by rewrite orbAC orbC orbA orbAC. 
  rewrite wf_re_CAnd /=. apply/and4P; split.
  rewrite andbT. apply/negP; rewrite mem_seq1 => heq2. move :heq.
  rewrite (eqP heq2). by rewrite compare_refl.
  rewrite andbT. move : heq ; rewrite /cregexp_le /leS /cmpS /= compare_neg.
  by case_eq (compare r2 r1).  by rewrite hw2. by rewrite andbT.
move: hw3. rewrite !wf_re_CAnd. case/and4P => h3 h4 h5. move/allP => h6.
apply/and4P; split.
apply (@leq_trans (size l3)). done.
rewrite (@perm_size _ (undup (merge' [::r1] (sort' l3)))
        (undup ([::r1]++l3))).
rewrite -{1}(@undup_id _ l3). by apply tool_undup_size. done.
apply uniq_perm. by apply undup_uniq. by apply undup_uniq. move => u.
by rewrite !mem_undup mem_merge !mem_cat mem_sort !mem_seq1.
by apply undup_uniq. apply sorted_undup. by apply leS_trans.
apply merge_sorted. by apply leS_total. done. apply sort_sorted.
by apply leS_total. apply/allP => x. 
rewrite mem_undup mem_merge mem_cat mem_sort mem_seq1.
case/orP => hu. by rewrite (eqP hu).  by apply : h6.
Qed.

Lemma mkPlusAC_nplus_nplus_nplus : forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 ->
 (r1 != CVoid /\ (forall l, r1 != CPlus l)) ->
 (r2 != CVoid /\ (forall l, r2 != CPlus l)) ->
 (r3 != CVoid /\ (forall l, r3 != CPlus l)) -> 
mkPlus (mkPlus r1 r2) r3 = mkPlus (mkPlus r1 r3) r2.
Proof.
move => r1 r2 r3 hw1 hw2 hw3 hh1 hh2 hh3.
rewrite (@toolmkPlus3 r1 r2) ?(@toolmkPlus3 r1 r3) => //.
case_eq (compare r1 r2) => heq1 //.
- case_eq (compare r1 r3) => heq2.
  + by rewrite -(compare_eq_axiom heq1) -(compare_eq_axiom heq2).
  + rewrite toolmkPlus3 ?mkPlus_unfold2 ?heq2 => //. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    simpl. by rewrite andbT /cregexp_le /leS /cmpS /= heq2.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done.
    apply uniq_perm. simpl. rewrite andbT. apply/negP. 
    rewrite mem_seq1 => h. move : heq2.
    by rewrite (eqP h) compare_refl. by apply undup_uniq. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq1). by rewrite orbAC orbb orbC.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq2. 
    by rewrite hw1 hw3.
  + rewrite toolmkPlus3 ?mkPlus_unfold2 ?heq2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. simpl. 
    by rewrite andbT /cregexp_le /leS /cmpS /= compare_neg heq2.
    apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply uniq_perm. simpl. rewrite andbT. apply/negP. 
    rewrite mem_seq1 => h. move : heq2.
    by rewrite (eqP h) compare_refl. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    rewrite (compare_eq_axiom heq1). by rewrite -orbA orbb.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq2.
    by rewrite hw1 hw3.
- case_eq (compare r1 r3) => heq2 //.
  + rewrite mkPlus_unfold2 ?toolmkPlus3 => //. rewrite heq1. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. simpl. rewrite andbT. 
    by rewrite /cregexp_le /leS /cmpS /= heq1.
    apply uniq_perm. by apply undup_uniq. simpl. rewrite andbT. 
    apply/negP. rewrite mem_seq1 => h. move : heq1.
    by rewrite (eqP h) compare_refl. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq2). by rewrite orbAC orbb orbC.
    rewrite wf_re_CPlus. apply/and4P; split => //=. 
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq1. 
    by rewrite hw1 hw2.
  + rewrite !mkPlus_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbAC. 
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq2. 
    by rewrite hw1 hw3.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq1. 
   by rewrite hw1 hw2.
  + rewrite !mkPlus_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbC orbA.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq2.
    by rewrite hw1 hw3.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq1.
    by rewrite hw1 hw2.
- case_eq (compare r1 r3) => heq2 //.
  + rewrite mkPlus_unfold2 ?toolmkPlus3 => //. rewrite heq1. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. simpl. rewrite andbT. 
    by rewrite /cregexp_le /leS /cmpS /= compare_neg heq1.
    apply uniq_perm. by apply undup_uniq. simpl. rewrite andbT. 
    apply/negP. rewrite mem_seq1 => h. move : heq1.
    by rewrite (eqP h) compare_refl. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq2). by rewrite -orbA orbC orbb orbC.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq1. 
    by rewrite hw2 hw1.
  + rewrite !mkPlus_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite -orbA orbC.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq2. 
    by rewrite hw1 hw3.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq1. 
    by rewrite hw2 hw1.
  + rewrite !mkPlus_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbC orbAC orbA.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq2.
     by rewrite hw3 hw1.
    rewrite wf_re_CPlus. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= compare_neg heq1.
    by rewrite hw2 hw1.
Qed.

Lemma mkAndAC_nand_nand_nand : forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 ->
 [/\ r1 != CVoid , r1 != CNot CVoid & (forall l, r1 != CAnd l)] ->
 [/\ r2 != CVoid , r2 != CNot CVoid & (forall l, r2 != CAnd l)] ->
 [/\ r3 != CVoid , r3 != CNot CVoid & (forall l, r3 != CAnd l)] -> 
mkAnd (mkAnd r1 r2) r3 = mkAnd (mkAnd r1 r3) r2.
Proof.
move => r1 r2 r3 hw1 hw2 hw3 hh1 hh2 hh3.
rewrite (@toolmkAnd3 r1 r2) ?(@toolmkAnd3 r1 r3) => //.
case_eq (compare r1 r2) => heq1 //.
- case_eq (compare r1 r3) => heq2.
  + by rewrite -(compare_eq_axiom heq1) -(compare_eq_axiom heq2).
  + rewrite toolmkAnd3 ?mkAnd_unfold2 ?heq2 => //. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    simpl. by rewrite andbT /cregexp_le /leS /cmpS /=  heq2.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. simpl.
    apply uniq_perm. simpl. rewrite andbT. apply/negP. 
    rewrite mem_seq1 => h. move : heq2.
    by rewrite (eqP h) compare_refl. by apply undup_uniq. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq1). by rewrite orbAC orbb orbC.
    rewrite wf_re_CAnd. apply/and4P; split => //=. 
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  heq2. 
    by rewrite hw1 hw3.
  + rewrite toolmkAnd3 ?mkAnd_unfold2 ?heq2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. simpl.
    by rewrite andbT /cregexp_le /leS /cmpS /=  compare_neg heq2.
    apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply uniq_perm. simpl. rewrite andbT. apply/negP. 
    rewrite mem_seq1 => h. move : heq2.
    by rewrite (eqP h) compare_refl. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    rewrite (compare_eq_axiom heq1). by rewrite -orbA orbb.
    rewrite wf_re_CAnd. apply/and4P; split => //=. 
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq2. 
    by rewrite hw1 hw3.
- case_eq (compare r1 r3) => heq2 //.
  + rewrite mkAnd_unfold2 ?toolmkAnd3 => //. rewrite heq1. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. simpl. rewrite andbT. 
    by rewrite /cregexp_le /leS /cmpS /=  heq1.
    apply uniq_perm. by apply undup_uniq. simpl. rewrite andbT. 
    apply/negP. rewrite mem_seq1 => h. move : heq1.
    by rewrite (eqP h) compare_refl. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq2). by rewrite orbAC orbb orbC.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  heq1. 
    by rewrite hw1 hw2.
  + rewrite !mkAnd_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbAC. 
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq2. 
    by rewrite hw1 hw3.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /= heq1.
    by rewrite hw1 hw2.
  + rewrite !mkAnd_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbC orbA.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq2.
    by rewrite hw3 hw1.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  heq1. 
    by rewrite hw1 hw2.
- case_eq (compare r1 r3) => heq2 //.
  + rewrite mkAnd_unfold2 ?toolmkAnd3 => //. rewrite heq1. f_equal.
    apply (@sorted_eq _ cregexp_le). by apply leS_trans. 
    by apply leS_antisym.
    apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. simpl. rewrite andbT. 
    by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq1.
    apply uniq_perm. by apply undup_uniq. simpl. rewrite andbT. 
    apply/negP. rewrite mem_seq1 => h. move : heq1.
    by rewrite (eqP h) compare_refl. move => u.  
    rewrite mem_undup mem_merge mem_cat mem_sort !mem_seq2 mem_seq1.
    rewrite (compare_eq_axiom heq2). by rewrite -orbA orbC orbb orbC.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq1.
    by rewrite hw1 hw2.
  + rewrite !mkAnd_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite -orbA orbC.
    rewrite wf_re_CAnd. apply/and4P; split => //=. 
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  heq2.
    by rewrite hw1 hw3. 
    rewrite wf_re_CAnd. apply/and4P; split => //=. 
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq1.
    by rewrite hw1 hw2.
  + rewrite !mkAnd_unfold2 => //. f_equal.
    apply : (@sorted_eq _ cregexp_le). by apply leS_trans.
    by apply leS_antisym. apply sorted_undup. by apply leS_trans.
    apply merge_sorted. by apply leS_total. apply sort_sorted. 
    by apply leS_total.
    done. apply sorted_undup. by apply leS_trans. apply merge_sorted. 
    by apply leS_total.
    apply sort_sorted. by apply leS_total. done. apply uniq_perm.
    by apply undup_uniq. by apply undup_uniq. move => u. 
    rewrite !mem_undup !mem_merge !mem_cat !mem_sort !mem_seq2 !mem_seq1.
    by rewrite orbC orbAC orbA.
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq2. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq2.
    by rewrite hw1 hw3. 
    rewrite wf_re_CAnd. apply/and4P; split => //=.
    rewrite andbT. apply/negP; rewrite mem_seq1 => heq. move: heq1. 
    by rewrite (eqP heq) compare_refl.
    rewrite andbT. by rewrite /cregexp_le /leS /cmpS /=  compare_neg heq1.
    by rewrite hw1 hw2.
Qed.

(* end hide *)
(** mkPlus and mkAnd are associative-commutative *)

Lemma mkPlusAC: forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 -> 
  mkPlus (mkPlus r1 r2) r3 = mkPlus (mkPlus r1 r3) r2.
Proof.
move => r1 r2 r3.
case: (toolmkPlus r1).
- move => heq; rewrite (eqP heq); clear heq r1. rewrite !mkPlus_CVoid_lt. by rewrite mkPlusC.
- case => l1 heq; rewrite (eqP heq); clear heq r1. move => hw1. case: (toolmkPlus r2).
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkPlus_CVoid_rt.
  + case => l2 heq; rewrite (eqP heq); clear heq r2. move => hw2.
    case : (toolmkPlus r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkPlus_CVoid_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkPlusAC_plus_plus_plus.
    * move => hh1 hw3. by rewrite mkPlusAC_plus_plus_nplus.
  + move => hh1 hw2. case: (toolmkPlus r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkPlus_CVoid_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkPlusAC_plus_plus_nplus.
      move => hh2 hw3. rewrite !(mkPlusC (CPlus l1) _ ).  
      rewrite -!mkPlusAC_nplus_nplus_plus => //.
      by rewrite (mkPlusC r2 r3).
- move => hh1 hw1. case: (toolmkPlus r2).
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkPlus_CVoid_rt.
  + case => l2 heq; rewrite (eqP heq) => hw2; clear heq r2.
    case : (toolmkPlus r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkPlus_CVoid_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      rewrite !(mkPlusC r1).
      rewrite -!mkPlusAC_plus_plus_nplus => //.
      by rewrite (mkPlusC (CPlus l2) (CPlus l3)).
    * move => hh3 hw3. by rewrite mkPlusAC_nplus_nplus_plus.
  + move => hh2 hw2. case: (toolmkPlus r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkPlus_CVoid_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkPlusAC_nplus_nplus_plus.
    * move => hh3 hw3. by rewrite mkPlusAC_nplus_nplus_nplus.
Qed.

Lemma mkAndAC: forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 -> 
  mkAnd (mkAnd r1 r2) r3 = mkAnd (mkAnd r1 r3) r2.
Proof.
move => r1 r2 r3.
case: (toolmkAnd r1).
- move => heq; rewrite (eqP heq); clear heq r1. by rewrite !mkAnd_CVoid_lt.
- move => heq; rewrite (eqP heq); clear heq r1. by rewrite !mkAnd_CAll_lt mkAndC.
- case => l1 heq; rewrite (eqP heq); clear heq r1. move => hw1. case: (toolmkAnd r2).
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkAnd_CVoid_rt.
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkAnd_CAll_rt.
  + case => l2 heq; rewrite (eqP heq); clear heq r2. move => hw2.
    case : (toolmkAnd r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CVoid_rt.
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CAll_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkAndAC_and_and_and.
    * move => hh1 hw3. by rewrite mkAndAC_and_and_nand.
  + move => hh1 hw2. case: (toolmkAnd r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CVoid_rt.
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CAll_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkAndAC_and_and_nand.
    * move => hh3 hw3. rewrite !(mkAndC (CAnd l1) _ ).  
      rewrite -!mkAndAC_nand_nand_and => //.
      by rewrite (mkAndC r2 r3).
- move => hh1 hw1. case: (toolmkAnd r2).
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkAnd_CVoid_rt.
  + move => heq; rewrite (eqP heq); clear heq r2. by rewrite !mkAnd_CAll_rt.
  + case => l2 heq; rewrite (eqP heq) => hw2; clear heq r2.
    case : (toolmkAnd r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CVoid_rt.
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CAll_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      rewrite !(mkAndC r1).
      rewrite -!mkAndAC_and_and_nand => //.
      by rewrite (mkAndC (CAnd l2) (CAnd l3)).
    * move => hh2 hw3. by rewrite mkAndAC_nand_nand_and.
  + move => hh2 hw2. case: (toolmkAnd r3).
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CVoid_rt.
    * move => heq; rewrite (eqP heq); clear heq r3. by rewrite !mkAnd_CAll_rt.
    * case => l3 heq ; rewrite (eqP heq) => hw3 ; clear heq r3.
      by rewrite mkAndAC_nand_nand_and.
    * move => hh3 w3. by rewrite mkAndAC_nand_nand_nand.
Qed.

(** mkPlus, mkAnd and mkConc are associative *)

Lemma mkPlusA : forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 ->
  mkPlus (mkPlus r1 r2) r3 = mkPlus r1 (mkPlus r2 r3).
Proof.
move => r1 r2 r3 h1 h2 h3.
rewrite mkPlusAC => //. rewrite (mkPlusC r1 r3).
rewrite -mkPlusAC => //. by rewrite (mkPlusC r3 r2) mkPlusC.
Qed.

Lemma mkAndA : forall r1 r2 r3, wf_re r1 -> wf_re r2 -> wf_re r3 ->
  mkAnd (mkAnd r1 r2) r3 = mkAnd r1 (mkAnd r2 r3).
Proof.
move => r1 r2 r3 h1 h2 h3.
rewrite mkAndAC => //. rewrite (mkAndC r1 r3).
rewrite -mkAndAC => //. by rewrite (mkAndC r3 r2) mkAndC.
Qed.

Lemma mkConcA : forall r1 r2 r3, mkConc (mkConc r1 r2) r3 = mkConc r1 (mkConc r2 r3).
Proof.
move => r1 r2 r3.  case: (toolmkConc r1).
- by move => heq; rewrite (eqP heq) !mkConc_CVoid_lt.
- by move => heq; rewrite (eqP heq) !mkConc_CEps_lt.
- case => l heq; rewrite (eqP heq). case: (toolmkConc r2).
  * by move => heq2; rewrite (eqP heq2) !mkConc_CVoid_lt.
  * by move => heq2; rewrite (eqP heq2) !mkConc_CEps_lt.
  * case => l2 heq2; rewrite (eqP heq2). rewrite {2}/mkConc.
    case: (toolmkConc r3).
    + by move => heq3; rewrite (eqP heq3) !mkConc_CVoid_rt.
    + by move => heq3; rewrite (eqP heq3) !mkConc_CEps_rt.
    + by case => l3 heq3; rewrite (eqP heq3) /mkConc catA.
    + case => h1 h2 h3. rewrite !(@mkConc_unfold _ r3) => //.
      by rewrite /mkConc catA.
  * case => h1 h2 h3. rewrite mkConc_unfold => //.
    case: (toolmkConc r3).
    + by move => heq3; rewrite (eqP heq3) !mkConc_CVoid_rt.
    + by move => heq3; rewrite (eqP heq3) !mkConc_CEps_rt mkConc_unfold.
    + case => l3 heq3; rewrite (eqP heq3) (@mkConc_unfold2  _ r2) /mkConc => //.
      by rewrite  -catA.
    + case => h'1 h'2 h'3. rewrite (@mkConc_unfold3 r2 r3)=> //.
      rewrite  (@mkConc_unfold _ r3) /mkConc => //.
      by rewrite -catA.
- case => h1 h2 h3. case: (toolmkConc r2).
  * by move => heq2; rewrite (eqP heq2) !mkConc_CVoid_lt !mkConc_CVoid_rt mkConc_CVoid_lt.
  * by move => heq2; rewrite (eqP heq2) mkConc_CEps_rt !mkConc_CEps_lt.
  * case => l2 heq2; rewrite (eqP heq2). rewrite mkConc_unfold2 => //.
    case: (toolmkConc r3).
    + by move => heq3; rewrite (eqP heq3) !mkConc_CVoid_rt.
    + by move => heq3; rewrite (eqP heq3) !mkConc_CEps_rt mkConc_unfold2 => //.
    + by case => l3 heq3; rewrite (eqP heq3) !(@mkConc_unfold2 _ r1) => //.
    + case => h'1 h'2 h'3. rewrite !(@mkConc_unfold _ r3) => //.
      by rewrite mkConc_unfold2.
  * case => h'1 h'2 h'3. rewrite (@mkConc_unfold3 r1 r2) => //.
    case: (toolmkConc r3).
    + by move => heq3; rewrite (eqP heq3) !mkConc_CVoid_rt.
    + by move => heq3; rewrite (eqP heq3) !mkConc_CEps_rt mkConc_unfold3.
    + case => l3 heq3; rewrite (eqP heq3) (@mkConc_unfold2 _ r2) // (@mkConc_unfold2 _ r1) => //.
    + case => h''1 h''2 h''3. rewrite (@mkConc_unfold3 r2 r3)=> //.
      rewrite (@mkConc_unfold2 _ r1) => //. by rewrite  (@mkConc_unfold _ r3) => //.
Qed.

(* begin hide *)

(* mix of C and id *)
Lemma mkPlus_dup : forall r1 r2, wf_re r1 -> wf_re r2 -> 
  mkPlus (mkPlus r1 r2) r2 = mkPlus r1 r2.
Proof.
move => r1 r2 h1 h2.
by rewrite (mkPlusC r1 r2) mkPlusAC ?mkPlus_id.
Qed.

Lemma mkAnd_dup : forall r1 r2, wf_re r1 -> wf_re r2 -> 
  mkAnd (mkAnd r1 r2) r2 = mkAnd r1 r2.
Proof.
move => r1 r2 h1 h2.
by rewrite (mkAndC r1 r2) mkAndAC ?mkAnd_id.
Qed.



End RegExpSim.

(** Compatibility definition to use in ex.v *)

Definition cmpb (a b: bool) : comparison := match a,b with
 | true,true => Eq
 | true,false => Gt
 | false,false => Eq
 | false,true => Lt
end.

Lemma cmpb_refl : forall b, cmpb b b = Eq.
Proof.
by case.
Qed.

Lemma cmpb_eq_axiom : forall a b, reflect (a=b) (cmpb a b == Eq).
Proof.
move => a b; apply: (iffP idP). by case: a b => [] [].
move => -> /=. by case: b.
Qed.

Lemma cmpb_trans : forall (s t u:bool) (x:comparison), 
  cmpb s t = x -> cmpb t u = x -> cmpb s u = x.
Proof.
case => [] [] [] //=.
by move => x <-.
by move => x <-.
Qed.

Lemma cmpb_neg : forall (s t:bool), cmpb t s = CompOpp (cmpb s t).
Proof.
by case => [] [] /=.
Qed.


Definition bool_osym_module_mixin := OSymModuleMixin cmpb_refl cmpb_eq_axiom cmpb_trans cmpb_neg.
Definition bool_osym_module := OSymModule bool_osym_module_mixin.

Canonical Structure bool_osym_module.



Definition ssim2 :
  regular_expression [eqType of bool] -> 
  regular_expression [eqType of bool] -> bool 
:= @similar bool_osym_module.


Lemma ssim2_Plus_id  : forall c : regular_expression [eqType of bool],
  ssim2 (Plus c c) c.
Proof.
rewrite /ssim2 /similar => c /=.
rewrite mkPlus_id => //.
by apply wf_re_can.

Qed.

Lemma ssim2_PlusC :forall c1 c2 : regular_expression [eqType of bool],
        ssim2 (Plus c1 c2) (Plus c2 c1).
Proof.
by rewrite /ssim2 /similar => c d /=; rewrite mkPlusC. 
Qed.

Lemma ssim2_PlusA : forall c1 c2 c3 : regular_expression [eqType of bool],
        ssim2 (Plus (Plus c1 c2) c3) (Plus c1 (Plus c2 c3)).
Proof.
rewrite /ssim2 /similar => c d e /=. 
rewrite mkPlusA => //; by apply wf_re_can.
Qed.

Lemma ssim2_congr_Conc : forall a b c d : bregexp,
        ssim2 a b -> ssim2 c d -> ssim2 (Conc a c) (Conc b d).
Proof.
rewrite /ssim2 /similar => s1 s2 s3 s4 heq1 heq2 /=.
by rewrite (eqP heq1) (eqP heq2).
Qed.


Lemma ssim2_congr_Plus: forall a b c d : bregexp,
        ssim2 a b -> ssim2 c d -> ssim2 (Plus a c) (Plus b d).
Proof.
rewrite /ssim2 /similar => s1 s2 s3 s4 heq1 heq2 /=.
by rewrite (eqP heq1) (eqP heq2).
Qed.


Lemma ssim2_congr_And : forall a b c d : bregexp,
        ssim2 a b -> ssim2 c d -> ssim2 (And a c) (And b d).
Proof.
rewrite /ssim2 /similar => s1 s2 s3 s4 heq1 heq2 /=.
by rewrite (eqP heq1) (eqP heq2).
Qed.

Lemma ssim2_congr_Star : forall a b : bregexp,
  ssim2 a b -> ssim2 (Star a) (Star b).
Proof.
by rewrite /ssim2 /similar => s1 s2 heq /=; rewrite (eqP heq).
Qed.

Lemma ssim2_congr_Not : forall a b : bregexp,
 ssim2 a b -> ssim2 (Not a) (Not b).
by rewrite /ssim2 /similar => s1 s2 heq /=; rewrite (eqP heq).
Qed.


Global Instance ssim2_Eq : Equivalence ssim2.
split.
red; by move => r; rewrite /ssim2 /similar.
red;  move => r s. by rewrite /ssim2 /similar => h; rewrite (eqP h).
red; move => r s t; rewrite /ssim2 /similar => heq1 heq2; 
  by rewrite (eqP heq1).
Qed.

Definition sim2_finite_number_of_der :=
  finite_number_of_der  
  ssim2_Plus_id  ssim2_PlusC  ssim2_PlusA 
  ssim2_congr_Conc  ssim2_congr_Plus  ssim2_congr_And 
  ssim2_congr_Star  ssim2_congr_Not.


Definition sim2_build_list_fun :=
  build_list_fun 
  ssim2_Plus_id  ssim2_PlusC  ssim2_PlusA 
  ssim2_congr_Conc  ssim2_congr_Plus  ssim2_congr_And 
  ssim2_congr_Star  ssim2_congr_Not.

Definition sim2_build_list_der :=
 build_list_der
  ssim2_Plus_id  ssim2_PlusC  ssim2_PlusA 
  ssim2_congr_Conc  ssim2_congr_Plus  ssim2_congr_And 
  ssim2_congr_Star  ssim2_congr_Not.

Definition sim2_bregexp_eq := 
  bregexp_eq
  ssim2_Plus_id  ssim2_PlusC  ssim2_PlusA 
  ssim2_congr_Conc  ssim2_congr_Plus  ssim2_congr_And 
  ssim2_congr_Star  ssim2_congr_Not.

Definition sim2_bregexp_sub :=
 bregexp_sub
  ssim2_Plus_id  ssim2_PlusC  ssim2_PlusA 
  ssim2_congr_Conc  ssim2_congr_Plus  ssim2_congr_And 
  ssim2_congr_Star  ssim2_congr_Not.
