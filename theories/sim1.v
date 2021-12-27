(* begin hide *)
From Coq Require Import RelationClasses Setoid Morphisms Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
From RegLang Require Import languages.
From RegexpBrzozowski Require Import regexp finite_der equiv.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.
(* end hide *)

(** "Naïve" implementation of similarity
    by a sort of "double inclusion" of regular expression.
    This implementation enjoys the minimal requirements
    of Brzozowski
*)
Section Similarity1.
Variable char : eqType.
Let regexp := regular_expression char.
Let word := word char.

Fixpoint ssubl (r1: regexp) {struct r1} : regexp -> bool := 
match r1 with
 | Void => fun r2 => true
 | Eps =>(fix ssubl' r2 := match r2 with
   | Eps => true 
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
   end
   ) 
 | Dot =>(fix ssubl' r2 := match r2 with
   | Dot => true 
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
   end
   ) 
 | Atom p =>(fix ssubl' r2 := match r2 with
   | Atom q => p == q  
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
   end
   ) 
 | Plus e f => fun r2 => ssubl e r2 && ssubl f r2
 | Conc e f => (fix ssubl' r2 := match r2 with
   | Conc e' f' => ssubl e e' && ssubl f f'
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
   end
   ) 
 | Star e => (fix ssubl' r2 := match r2 with
   | Star f => ssubl e f
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
     end
 )
 | And e f => (fix ssubl' r2 := match r2 with
   | And e' f' => ssubl e e' && ssubl f f'
   | Plus e' f' => ssubl' e' || ssubl' f'
   | _ => false
     end
 )
 | Not r1 => (fix ssubl'  r2 := match r2 with
    | Not r2 => ssubr r1 r2
    | Plus e' f' => ssubl' e' || ssubl' f'
    | _ => false
    end)
end
with ssubr (r1 : regexp) : regexp -> bool :=
 match r1 with
 | Void => (fix ssub' r2 := match r2 with
    | Void => true
    | Plus e' f' => ssub' e' && ssub' f'
     | _ => false end
)
 | Eps =>(fix ssub' r2 := match r2 with
   | Void => true
   | Eps => true 
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
   end
   ) 
 | Dot =>(fix ssub' r2 := match r2 with
   | Void => true
   | Dot => true 
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
   end
   ) 
 | Atom p =>(fix ssub' r2 := match r2 with
   | Void => true
   | Atom q => p == q  
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
   end
   ) 
 | Plus e f => (fix ssub' r2 := match r2 with
    | Plus e' f' => ssub' e' && ssub' f'
    | _ =>  ssubr e r2 || ssubr f r2
    end
  )
 | Conc e f => (fix ssub' r2 := match r2 with
   | Void => true
   | Conc e' f' => ssubr e e' && ssubr f f'
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
   end
   ) 
 | Star e => (fix ssub' r2 := match r2 with
   | Void => true
   | Star f => ssubr e f
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
     end
 )
 | And e f => (fix ssub' r2 := match r2 with
   | Void => true
   | And e' f' => ssubr e e' && ssubr f f'
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
     end
 )
 | Not r1 => (fix ssub' r2 := match r2 with
   | Void => true
   | Not r2 => ssubl r1 r2
   | Plus e' f' => ssub' e' && ssub' f'
   | _ => false
   end
  )
end.


Definition ssim1 r1 r2 := ssubl r1 r2 && ssubr r1 r2.

Lemma ssublStar : forall r s,  ssubl (Star r) (Star s) = ssubl r s.
Proof.
by move => r s /=.
Qed.

Lemma ssubrStar : forall r s,  ssubr (Star r) (Star s) = ssubr r s.
Proof.
by move => r s /=.
Qed.


Lemma ssublNot : forall r s,  ssubl (Not r) (Not s) = ssubr r s.
Proof.
by move => r s /=.
Qed.


Lemma ssubrNot : forall r s,  ssubr (Not r) (Not s) = ssubl r s.
Proof.
by move => r s /=.
Qed.


Lemma ssublConc : forall r1 r2 s1 s2, 
 ssubl (Conc r1 r2) (Conc s1 s2) = ssubl r1 s1 && ssubl r2 s2.
Proof.
by move => r1 r2 s1 s2 /=.
Qed.

Lemma ssubrConc : forall r1 r2 s1 s2, 
 ssubr (Conc r1 r2) (Conc s1 s2) = ssubr r1 s1 && ssubr r2 s2.
Proof.
by move => r1 r2 s1 s2 /=.
Qed.

Lemma ssublAnd : forall r1 r2 s1 s2, 
 ssubl (And r1 r2) (And s1 s2) = ssubl r1 s1 && ssubl r2 s2.
Proof.
by move => r1 r2 s1 s2 /=.
Qed.

Lemma ssubrAnd : forall r1 r2 s1 s2, 
 ssubr (And r1 r2) (And s1 s2) = ssubr r1 s1 && ssubr r2 s2.
Proof.
by move => r1 r2 s1 s2 /=.
Qed.

Lemma ssublVoid : forall r, ssubl (Void char) r.
Proof.
by move => r /=.
Qed.

Lemma ssubrVoid : forall r, ssubr r (Void char).
Proof.
elim => //=.  
by move => r -> r' ->.
Qed.

Definition nPlus (r:regexp) := match r with
 | Plus _ _ => false
 | _ => true
end.

Lemma ssublPlus1 : forall r s0 s1, nPlus r -> 
 ssubl r (Plus s0 s1) = ssubl r s0  || ssubl r s1.
Proof.
by case.
Qed.

Lemma ssublPlus2 : forall r1 r2 s, 
 ssubl (Plus r1 r2) s = ssubl r1 s && ssubl r2 s.
Proof.
by move => r1 r2 /=.
Qed.

Lemma ssubrPlus1 : forall r s0 s1, nPlus r -> 
 ssubr (Plus s0 s1) r = ssubr s0 r  || ssubr s1 r.
Proof.
by case.
Qed.

Lemma ssubrPlus2 : forall r1 r2 s, 
 ssubr s (Plus r1 r2) = ssubr s r1 && ssubr s r2.
Proof.
move => r1 r2.
by case.
Qed.


Lemma ssublPlusl : forall r s t, ssubl r s -> ssubl r (Plus s t).
Proof.
move => r s t.
elim : r => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //; 
 try (by rewrite ssublPlus1 // => ->).
rewrite ssublPlus2.
case/andP => h1 h2 /=; by rewrite hc1 // hc2.
Qed.


Lemma ssublPlusr : forall r s t, ssubl r s -> ssubl r (Plus t s).
Proof.
move => r s t.
elim : r => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //; 
 try (by rewrite ssublPlus1 // => ->; rewrite orbT).
rewrite ssublPlus2.
case/andP => h1 h2 /=; by rewrite hc1 // hc2.
Qed.


Lemma ssubrPlusl : forall r s t, ssubr s r -> ssubr (Plus s t) r.
Proof.
move => r s t.
elim : r => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //; 
 try (by rewrite ssubrPlus1 // => ->).
rewrite !ssubrPlus2.
case/andP => h1 h2; by rewrite hc1 // hc2.
Qed.


Lemma ssubrPlusr : forall r s t, ssubr s r -> ssubr (Plus t s) r.
Proof.
move => r s t.
elim : r => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //; 
 try (by rewrite ssubrPlus1 // => ->; rewrite orbT).
rewrite !ssubrPlus2.
case/andP => h1 h2 ; by rewrite hc1 // hc2.
Qed.

Lemma ssublrV : forall r , ssubl r (Void char) = ssubr (Void char) r.
Proof.
elim => [ | | | a | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //.
by rewrite ssublPlus2 ssubrPlus2 hc1 hc2.
Qed.

Lemma ssublrE : forall r , ssubl r (Eps char) = ssubr (Eps char) r.
Proof.
elim => [ | | | a | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //.
by rewrite ssublPlus2 ssubrPlus2 hc1 hc2.
Qed.

Lemma ssublrD : forall r , ssubl r (Dot char) = ssubr (Dot char) r.
Proof.
elim => [ | | | a | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //.
by rewrite ssublPlus2 ssubrPlus2 hc1 hc2.
Qed.

Lemma ssublrA : forall r u, ssubl r (Atom u) = ssubr (Atom u) r.
Proof.
elim => [ | | | a | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] // u.
- by rewrite /= eq_sym.
by rewrite ssublPlus2 ssubrPlus2 hc1 hc2.
Qed.


Lemma ssubl_r : forall r,  (forall s, ssubl r s = ssubr s r) /\
 (forall s, ssubl s r = ssubr r s).
Proof.
elim => [ | | | a | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ].
- split. 
  + by move => s; rewrite !ssublVoid !ssubrVoid.
  by move => s; apply ssublrV.
- split. 
  + elim => // r1 hr1 r0 hr0.
    by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr0.
  by move => s; apply ssublrE.
- split.
  + elim => // r1 hr1 r0 hr0.
    by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr0.
  by move => s; apply ssublrD.
- split.
  + elim => //. 
    * move => b /=. by rewrite eq_sym. 
    move => r1 hr1 r0 hr0.
    by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr0.
  by move => s; apply ssublrA.
-  case: hc => hc1 hc2. split.
  + elim  => //. 
    * move => r h; by rewrite ssublStar ssubrStar (hc1 r).
    move => r1 hr1 r2 hr2. 
    by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr2.
  elim  => //. 
  +  move => r h; by rewrite ssublStar ssubrStar (hc2 r).
  move => r1 hr1 r2 hr2. 
  by rewrite ssublPlus2 ssubrPlus2 hr1 hr2.
- split; case: hc1 hc2 => hc11 hc12 [hc21 hc22]. 
  + move => s. by rewrite ssublPlus2 ssubrPlus2 (hc11 s) (hc21 s). 
  elim => [ | | | t | c' _ | c1' hc1' c2' hc2' |
     c1' _ c2' _ | c1' _ c2' _ | c' _ ] ; 
     try (by rewrite ssublPlus1 // ssubrPlus1 // hc12 hc22).
  by rewrite ssublPlus2 ssubrPlus2 hc1' hc2'.
- case: hc1 hc2 => hc11 hc12 [hc21 hc22]; split.
  + elim => //.
    * move => r1 hr1 r2 hr2.
      by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr2.
    move => r1 hr1 r2 hr2.
    by rewrite ssublAnd ssubrAnd (hc11 r1) (hc21 r2).
  elim  => //. 
  +  move => r1 h1 r2 h2. by rewrite ssublPlus2 ssubrPlus2 h1 h2. 
  move => r1 hr1 r2 hr2. 
  by rewrite ssublAnd ssubrAnd hc12 hc22. 
- case: hc1 hc2 => hc11 hc12 [hc21 hc22]; split.
  + elim => //.
    * move => r1 hr1 r2 hr2.
      by rewrite ssublPlus1 // ssubrPlus1 // hr1 hr2.
    move => r1 hr1 r2 hr2.
    by rewrite ssublConc ssubrConc (hc11 r1) (hc21 r2).
  elim  => //. 
  +  move => r1 h1 r2 h2. by rewrite ssublPlus2 ssubrPlus2 h1 h2. 
  move => r1 hr1 r2 hr2. 
  by rewrite ssublConc ssubrConc hc12 hc22. 
case: hc => hc1 hc2; split.
- elim => //.
  + move => r1 hr1 r2 hr2. by rewrite ssublPlus1 //ssubrPlus1 // hr1 hr2.
  move => r hr. by rewrite ssublNot ssubrNot hc2.
elim => //.
- move => r1 hr1 r2 hr2. by rewrite ssublPlus2 ssubrPlus2 hr1 hr2.
move => r hr. by rewrite ssublNot ssubrNot hc1.
Qed.

Lemma ssublr : forall r s, ssubl r s = ssubr s r.
Proof.
move => r s; apply ssubl_r.
Qed.

Lemma ssubl_refl : forall r, ssubl r r.
Proof.
elim => [ | | | s | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] // .
- by rewrite /= !eq_refl.
- rewrite ssublPlus2.
  by rewrite (ssublPlusl c2 hc1)  (ssublPlusr c1 hc2).
- by rewrite ssublAnd hc1 hc2.
- by rewrite ssublConc hc1 hc2.
by rewrite ssublNot -ssublr hc. 
Qed.

Lemma ssim1_refl : reflexive ssim1.
Proof.
rewrite /ssim1 => r.
by rewrite -ssublr !ssubl_refl.
Qed.

Lemma ssim1C : symmetric ssim1.
Proof.
rewrite /ssim1 => r s.
by rewrite !ssublr andbC. 
Qed.

Lemma ssim1_Plus_id : forall r, ssim1 (Plus r r) r.
Proof.
move => r; rewrite ssim1C /ssim1.
rewrite -ssublr.
rewrite ssublPlusl /=.
- by rewrite !ssubl_refl.
by rewrite ssubl_refl.
Qed.

Lemma ssim1_PlusC : forall r s, ssim1 (Plus r s) (Plus s r).
Proof.
rewrite /ssim1 => r s.
rewrite -ssublr /=.
rewrite ssublPlusr ?ssubl_refl => //=.
rewrite ssublPlusl ?ssubl_refl => //=.
rewrite ssublPlusr ?ssubl_refl => //=.
by rewrite ssublPlusl ?ssubl_refl.
Qed.

Lemma ssim1_PlusA : forall r s t, 
 ssim1 (Plus (Plus r s) t) (Plus r (Plus s t)).
Proof.
rewrite /ssim1 => r s t.
rewrite -ssublr /=.
apply/and4P; split.
- rewrite ssublPlusl ?ssubl_refl => //=.
  rewrite ssublPlusr ?ssubl_refl => //=.
  + rewrite ssublPlusr ?ssubl_refl => //=.
    by rewrite ssublPlusr ? ssubl_refl.
  by rewrite ssublPlusl ? ssubl_refl.
- rewrite ssublPlusl ?ssubl_refl => //=.
  by rewrite ssublPlusl ?ssubl_refl.
- rewrite ssublPlusl ?ssubl_refl => //=.
  by rewrite ssublPlusr ?ssubl_refl.
by rewrite ssublPlusr ?ssubl_refl.
Qed.


Lemma ssubr_transV : forall y z, 
 ssubr (Void char) y -> ssubr y z -> ssubr (Void char) z.
Proof.
elim => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] z //.
rewrite ssubrPlus2; case/andP => h1 h2.
elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _ ] //; try by( 
  rewrite ssubrPlus1 //; case/orP => hu; [rewrite hc1 | rewrite hc2]
).
rewrite !ssubrPlus2; case/andP => h3 h4.
by rewrite hc1' //  hc2'.
Qed.

Lemma ssubr_transE : forall y z, 
 ssubr (Eps char) y -> ssubr y z -> ssubr (Eps char) z.
Proof.
elim => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] z //.
- move => _; elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _] //.
  rewrite !ssubrPlus2; case/andP => h1 h2.
  by rewrite hc1' // hc2'.
rewrite ssubrPlus2; case/andP => h1 h2.
elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _ ] //; try by( 
  rewrite ssubrPlus1 //; case/orP => hu; [rewrite hc1 | rewrite hc2]
).
rewrite !ssubrPlus2; case/andP => h3 h4.
by rewrite hc1' //  hc2'.
Qed.

Lemma ssubr_transD : forall y z, 
 ssubr (Dot char) y -> ssubr y z -> ssubr (Dot char) z.
Proof.
elim => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] z //.
- move => _; elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _] //.
  rewrite !ssubrPlus2; case/andP => h1 h2.
  by rewrite hc1' // hc2'.
rewrite ssubrPlus2; case/andP => h1 h2.
elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _ ] //; try by( 
  rewrite ssubrPlus1 //; case/orP => hu; [rewrite hc1 | rewrite hc2]
).
rewrite !ssubrPlus2; case/andP => h3 h4.
by rewrite hc1' //  hc2'.
Qed.

Lemma ssubr_transA : forall u y z, 
 ssubr (Atom u) y -> ssubr y z -> ssubr (Atom u) z.
Proof.
move => u. elim => [ | | | v | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] z //.
- move => _; elim : z => [ | | | w | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _] //.
  rewrite !ssubrPlus2; case/andP => h1 h2.
  by rewrite hc1' // hc2'.
- by rewrite {1}/ssubr => h; rewrite (eqP h).
rewrite ssubrPlus2; case/andP => h1 h2.
elim : z => [ | | | w | c' _ | c1' hc1' c2' hc2' | 
  c1' _ c2' _ | c1' _ c2' _ | c _ ] //; try by( 
  rewrite ssubrPlus1 //; case/orP => hu; [rewrite hc1 | rewrite hc2]
).
rewrite !ssubrPlus2; case/andP => h3 h4.
by rewrite hc1' //  hc2'.
Qed.


Lemma ssublr_trans : forall y x z, 
  (ssubl x y -> ssubl y z -> ssubl x z) /\ 
  ( ssubr x y -> ssubr y z -> ssubr x z).
Proof.
move => y x.
elim : x y => [ | | | u | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //.
- move => y z. rewrite !ssublVoid.
  split; first trivial.
  by apply ssubr_transV.
- elim => [ | | | v | c _ | c1 hc1 c2 hc2 | 
  c1 _ c2 _ | c1 _ c2 _ | c _ ] z //.
  + split; first done.
    by apply ssubr_transE.
  case: (hc1 z) (hc2 z) => h11 h12 [h21 h22]; split.
  + rewrite ssublPlus1 // ssublPlus2.
    case/orP => hu; case/andP => h1 h2; [ by apply: h11 | by apply: h21].
  by apply ssubr_transE.
- elim => [ | | | v | c _ | c1 hc1 c2 hc2 | 
  c1 _ c2 _ | c1 _ c2 _ | c _ ] z //.
  + split; first done.
    by apply ssubr_transD.
  case: (hc1 z) (hc2 z) => hc11 hc12 [hc21 hc22]; split.
  + rewrite ssublPlus1 // ssublPlus2.
    case/orP => hu; case/andP => h1 h2; [ by apply: hc11 | by apply: hc21].
  by apply ssubr_transD.
- elim => [ | | | v | c _ | c1 hc1 c2 hc2 | 
  c1 _ c2 _ | c1 _ c2 _ | c _ ] z //.
  + split; first done.
    by apply ssubr_transA.
  + by split; [
     rewrite [ssubl (Atom _) (Atom _)]/= => heq; rewrite (eqP heq) |
     rewrite [ssubr (Atom _) (Atom _)]/= => heq; rewrite (eqP heq)].
  case: (hc1 z) (hc2 z) => hc11 hc12 [hc21 hc22]; split.
  + rewrite ssublPlus1 // ssublPlus2.
    case/orP => hu; case/andP => h1 h2; [ by apply: hc11 | by apply: hc21].
  by apply ssubr_transA.
- elim => [ | | | v | c' hc' | c'1 hc'1 c'2 hc'2 | 
  c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ] //.
  + split; first done.
    elim : z => // r1 hr1 r2 hr2 _.
    rewrite !ssubrPlus2; case/andP => h1 h2.
    by rewrite hr1 // hr2.
  + rewrite ssublStar ssubrStar. elim => //.
    * move => c''; rewrite !ssublStar !ssubrStar => [[h11 h12]].
      by apply: hc.
    move => r1 [hr11 hr12] r2 [hr21 hr22]. split. 
    * rewrite !ssublPlus1 // => h1.
      case/orP => hu; apply/orP; 
        [ left; by apply hr11 | right; by apply hr21].
    rewrite !ssubrPlus2 => h1. case/andP => h2 h3.
    by rewrite hr12 // hr22.
  move => z; rewrite ssublPlus1 // ssublPlus2 ssubrPlus2.
  split.
  + case/orP => hu; case/andP => h1 h2; [ by apply hc'1 | by apply hc'2].
  case/andP => h1 h2.
  elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
    c1' _ c2' _ | c1' _ c2' _ | c' _ ] //; try by( 
    rewrite ssubrPlus1 //; case/orP => hu; [apply hc'1 | apply hc'2]
  ).
  rewrite !ssubrPlus2; case/andP => h3 h4.
  by rewrite hc1' //  hc2'.
- move => y z; split. 
  + case: (hc1 y z)  (hc2 y z) => hy1 _ [hz1 _].
    clear hc1 hc2 .
    elim : y hy1 hz1 => [ | | | v | c' _ | c'1 hc'1 c'2 hc'2 | 
      c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ] hy1 hz1; 
       rewrite !ssublPlus2; case/andP => h1 h2 h; 
       by rewrite (hy1 h1) // (hz1 h2).
  have h1 : forall y z, ssubr c1 y -> ssubr y z -> ssubr c1 z.
  + by apply hc1.
  have h2 : forall y z, ssubr c2 y -> ssubr y z -> ssubr c2 z.
  + by apply hc2.
  clear hc1 hc2.
  move : z.
  elim : y => [ | | | v | c' _ | c'1 hc'1 c'2 hc'2 | 
      c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ]z ; try (
    by rewrite ssubrPlus1 //; case/orP => hu h;
   [ apply ssubrPlusl; apply (h1 _ _ hu) |
     apply ssubrPlusr; apply (h2 _ _ hu)]).
  rewrite !ssubrPlus2; case/andP => h3 h4.
  elim : z  => [ | | | v | d _ | d1 hd1 d2 hd2 | 
      d1 _ d2 _ | d1 _ d2 _ | d _ ] ; try(
  by rewrite ssubrPlus1 //; case/orP => hu; [apply hc'1 | apply hc'2]
  ).
  rewrite !ssubrPlus2; case/andP => g3 g4.
  by rewrite hd1 // hd2.
- elim => [ | | | v | c' hc' | c'1 hc'1 c'2 hc'2 | 
  c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ] //.
  + split; first done.
    elim : z => // r1 hr1 r2 hr2 _.
    rewrite !ssubrPlus2; case/andP => h1 h2.
    by rewrite hr1 // hr2.
  + move => z; rewrite ssublPlus1 // ssublPlus2 ssubrPlus2.
    split.
    * case/orP => hu; case/andP => h1 h2; [ by apply hc'1 | by apply hc'2].
    case/andP => h1 h2.
    elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
      c1' _ c2' _ | c1' _ c2' _ | c' _ ] //; try by( 
      rewrite ssubrPlus1 //; case/orP => hu; [apply hc'1 | apply hc'2]
    ).
    rewrite !ssubrPlus2; case/andP => h3 h4.
    by rewrite hc1' //  hc2'.
  rewrite ssublAnd ssubrAnd. elim => //.
  + move => r1 [hr11 hr12] r2 [hr21 hr22]; split.
    * rewrite !ssublPlus1 // => h1. 
      case/orP => hu; apply/orP; 
        [ left; by apply hr11 | right; by apply hr21].
    rewrite !ssubrPlus2 => h1. case/andP => h2 h3.
    by rewrite hr12 // hr22.  
  move => r1 [hr11 hr12] r2 [hr21 hr22]. split; case/andP => h1 h2. 
  + rewrite !ssublAnd; case/andP => h3 h4.
    by apply/andP; split; [apply (hc1 c'1 r1) | apply (hc2 c'2 r2)].
  rewrite !ssubrAnd; case/andP => h3 h4.
  by apply/andP; split; [apply (hc1 c'1 r1) | apply (hc2 c'2 r2)].
- elim => [ | | | v | c' hc' | c'1 hc'1 c'2 hc'2 | 
  c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ] //.
  + split; first done.
    elim : z => // r1 hr1 r2 hr2 _.
    rewrite !ssubrPlus2; case/andP => h1 h2.
    by rewrite hr1 // hr2.
  + move => z; rewrite ssublPlus1 // ssublPlus2 ssubrPlus2.
    split.
    * case/orP => hu; case/andP => h1 h2; [ by apply hc'1 | by apply hc'2].
    case/andP => h1 h2.
    elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
      c1' _ c2' _ | c1' _ c2' _ | c' _ ] //; try by( 
      rewrite ssubrPlus1 //; case/orP => hu; [apply hc'1 | apply hc'2]
    ).
    rewrite !ssubrPlus2; case/andP => h3 h4.
    by rewrite hc1' //  hc2'.
  rewrite ssublConc ssubrConc. elim => //.
  + move => r1 [hr11 hr12] r2 [hr21 hr22]; split.
    * rewrite !ssublPlus1 // => h1. 
      case/orP => hu; apply/orP; 
        [ left; by apply hr11 | right; by apply hr21].
    rewrite !ssubrPlus2 => h1. case/andP => h2 h3.
    by rewrite hr12 // hr22.  
  move => r1 [hr11 hr12] r2 [hr21 hr22]. split; case/andP => h1 h2. 
  + rewrite !ssublConc; case/andP => h3 h4.
    by apply/andP; split; [apply (hc1 c'1 r1) | apply (hc2 c'2 r2)].
  rewrite !ssubrConc; case/andP => h3 h4.
  by apply/andP; split; [apply (hc1 c'1 r1) | apply (hc2 c'2 r2)].
elim => [ | | | v | c' hc' | c'1 hc'1 c'2 hc'2 | 
  c'1 _ c'2 _ | c'1 _ c'2 _ | c' _ ] //.
- split; first done.
  elim : z => // r1 hr1 r2 hr2 _.
  rewrite !ssubrPlus2; case/andP => h1 h2.
  by rewrite hr1 // hr2.
- move => z; rewrite ssublPlus1 // ssublPlus2; split.
  * case/orP => hu; case/andP => h1 h2; [ by apply hc'1 | by apply hc'2].
  rewrite ssubrPlus2; case/andP => h1 h2.
  elim : z => [ | | | v | c' _ | c1' hc1' c2' hc2' | 
    c1' _ c2' _ | c1' _ c2' _ | c' _ ] //; try by( 
    rewrite ssubrPlus1 //; case/orP => hu; [apply hc'1 | apply hc'2]
  ).
  rewrite !ssubrPlus2; case/andP => h3 h4.
  by rewrite hc1' //  hc2'.
move => z. rewrite ssublNot ssubrNot. 
elim :z => //.
- move => r1 [hr11 hr12] r2 [hr21 hr22]. split => h1. 
  + rewrite !ssublPlus1 //.
    case/orP => hu; apply/orP; [left; by apply hr11 | right; by apply hr21].
  rewrite !ssubrPlus2; case/andP => h2 h3.
  by rewrite hr12 // hr22.
move => r [hr1 hr2]; rewrite !ssublNot !ssubrNot.  split => h1 h2.
- by apply (hc c' r). 
by apply (hc c' r).
Qed.



Lemma ssim1_congr_Star : forall a b, ssim1 a b -> ssim1 (Star a) (Star b).
Proof.
rewrite /ssim1 => a b; case/andP => h1 h2.
by rewrite ssublStar ssubrStar h1 h2.
Qed.

Lemma ssim1_congr_Not : forall a b, ssim1 a b -> ssim1 (Not a) (Not b).
Proof.
rewrite /ssim1 => a b; case/andP => h1 h2.
by rewrite ssublNot ssubrNot h1 h2.
Qed.

Lemma ssim1_congr_Conc : forall a b c d, ssim1 a b -> ssim1 c d ->
  ssim1 (Conc a c) (Conc b d).
Proof.
rewrite /ssim1 => a b c d; case/andP => h1 h2; case/andP => h3 h4.
by rewrite ssublConc ssubrConc h1 h2 h3 h4.
Qed.

Lemma ssim1_congr_And : forall a b c d, ssim1 a b -> ssim1 c d ->
  ssim1 (And a c) (And b d).
Proof.
rewrite /ssim1 => a b c d; case/andP => h1 h2; case/andP => h3 h4.
by rewrite ssublAnd ssubrAnd h1 h2 h3 h4.
Qed.

Lemma ssim1_congr_Plus : forall a b c d, ssim1 a b -> ssim1 c d ->
  ssim1 (Plus a c) (Plus b d).
Proof.
rewrite /ssim1 => a b c d; case/andP => h1 h2; case/andP => h3 h4.
rewrite ssublPlus2 ssubrPlus2. 
rewrite ssublPlusl => //.
rewrite ssublPlusr => //.
rewrite ssubrPlusl => //.
by rewrite ssubrPlusr.
Qed.

Lemma ssubrVoid_ok : forall b, ssubr (Void char) b -> 
  forall x, (x \in b) -> (x \in (Void char)).
Proof.
elim => //.
move => r1 hr1 r2 hr2.  rewrite ssubrPlus2; case/andP => h1 h2 x.
rewrite -topredE /=; case/orP => hu.
- by apply: hr1.
by apply: hr2.
Qed.

Lemma ssublEps_ok : forall b, ssubl (Eps char) b ->
  forall x, (x \in (Eps char) ) -> (x \in b).
Proof.
elim => //.
move => r1 hr1 r2 hr2. rewrite ssublPlus1 //.
case/orP => hu x.
- rewrite -!topredE /= => hx.
  apply/orP; left. by apply: hr1.
rewrite -!topredE /= => hx.
apply/orP; right. by apply: hr2.
Qed.

Lemma ssubrEps_ok : forall b, ssubr (Eps char) b ->
  forall x, (x \in b) -> (x \in (Eps char) ).
Proof.
elim => //.
move => r1 hr1 r2 hr2. rewrite ssubrPlus2. 
case/andP => h1 h2 x.
rewrite -!topredE /=; case/orP => hu.
- move: (hr1 h1 x hu). by rewrite -topredE /=.
move: (hr2 h2 x hu). by rewrite -topredE /=.
Qed.

Lemma ssublDot_ok : forall b, ssubl (Dot char) b ->
  forall x, (x \in (Dot char) ) -> (x \in b).
Proof.
elim => //.
move => r1 hr1 r2 hr2. rewrite ssublPlus1 //.
case/orP => hu x.
- rewrite -!topredE /= => hx.
  apply/orP; left. by apply: hr1.
rewrite -!topredE /= => hx.
apply/orP; right. by apply: hr2.
Qed.

Lemma ssubrDot_ok : forall b, ssubr (Dot char) b ->
  forall x, (x \in b) -> (x \in (Dot char)).
Proof.
elim => //.
move => r1 hr1 r2 hr2. rewrite ssubrPlus2. 
case/andP => h1 h2 x.
rewrite -!topredE /=; case/orP => hu.
- move: (hr1 h1 x hu). by rewrite -topredE /=.
move: (hr2 h2 x hu). by rewrite -topredE /=.
Qed.

Lemma ssublAtom_ok : forall s b, ssubl (Atom s) b ->
  forall x, (x \in (Atom s) ) -> (x \in b).
Proof.
move => s; elim => //.
- by move => t; rewrite {1}/ssubl => h; rewrite (eqP h).
move => r1 hr1 r2 hr2. rewrite ssublPlus1 //.
case/orP => hu x.
- rewrite -!topredE /= => hx.
  apply/orP; left. by apply: hr1.
rewrite -!topredE /= => hx.
apply/orP; right. by apply: hr2.
Qed.

Lemma ssubrAtom_ok : forall s b, ssubr (Atom s) b ->
  forall x, (x \in b) -> (x \in (Atom s) ).
Proof.
move => s; elim => //.
- by move => t; rewrite {1}/ssubr => h; rewrite (eqP h).
move => r1 hr1 r2 hr2. rewrite ssubrPlus2. 
case/andP => h1 h2 x.
rewrite -!topredE /=; case/orP => hu.
- move: (hr1 h1 x hu). by rewrite -topredE /=.
move: (hr2 h2 x hu). by rewrite -topredE /=.
Qed.

Lemma ssublStar_ok : forall a, 
  (forall b, ssubl a b -> forall x, x \in a -> x \in b) ->
  forall b, ssubl (Star a) b -> 
  forall x, x \in (Star a) -> x \in b.
Proof.
move => a ha. 
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- rewrite ssublStar => h x. rewrite -!topredE /=. 
  case/starP => v. move/allP => h1 /= h2.  
  apply/starP; exists v => //.
  apply/allP => y hy.
  case/andP : (h1 y hy) => hy1 hy2.
  apply/andP; split => //.
  by rewrite inE (ha d h y).
by rewrite ssublPlus1 => //;
  case/orP => hu x hx;  rewrite -topredE /=; 
   apply/orP; [left; rewrite (hd1 hu x hx) | 
              right; rewrite (hd2 hu x hx)].
Qed.

Lemma ssubrStar_ok : forall a, 
  (forall b, ssubr a b -> forall x, x \in b -> x \in a) ->
  forall b, ssubr (Star a) b -> 
  forall x, x \in b -> x \in (Star a). 
Proof.
move => a ha. 
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- rewrite ssubrStar => h x. rewrite -!topredE /=. 
  case/starP => v. move/allP => h1 /= h2.  
  apply/starP; exists v => //.
  apply/allP => y hy.
  case/andP : (h1 y hy) => hy1 hy2.
  apply/andP; split => //.
  by rewrite inE (ha d h y).
by rewrite ssubrPlus2; case/andP => h1 h2 x;
  rewrite -topredE /=; case/orP => hx ; 
   [rewrite  (hd1 h1 x hx) |
    rewrite  (hd2 h2 x hx)].
Qed.

Lemma ssublNot_ok : forall a, 
  (forall b, ssubr a b -> forall x, x \in b -> x \in a) ->
  forall b, ssubl (Not a) b -> 
  forall x, x \in (Not a) -> x \in b.
Proof.
move => a ha. 
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- by rewrite ssublPlus1 => //;
       case/orP => hu x hx;  rewrite -topredE /=; 
       apply/orP; [left; rewrite (hd1 hu x hx) | 
                   right; rewrite (hd2 hu x hx)].
rewrite ssublNot => h x. rewrite -topredE /= /compl /=; move/negP=> h1.
rewrite -topredE /= /compl /=. apply/negP => hn.
apply: h1.
by apply (ha d h x hn).
Qed.

Lemma ssubrNot_ok : forall a, 
  (forall b, ssubl a b -> forall x, x \in a -> x \in b) ->
  forall b, ssubr (Not a) b -> 
  forall x, x \in b -> x \in (Not a). 
Proof.
move => a ha. 
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- by rewrite ssubrPlus2; case/andP => h1 h2 x;
     rewrite -topredE /=; case/orP => hx ; 
      [rewrite  (hd1 h1 x hx) |
       rewrite  (hd2 h2 x hx)].
rewrite ssubrNot => h x. rewrite -topredE /= /compl /=; move/negP=> h1.
rewrite -topredE /= /compl /=. apply/negP => hn.
apply: h1.
by apply (ha d h x hn).
Qed.

Lemma ssublPlus_ok : forall a c, 
  (forall b, ssubl a b -> forall x, x \in a -> x \in b) ->
  (forall d, ssubl c d -> forall x, x \in c -> x \in d) ->
  forall r, ssubl (Plus a c) r -> 
  forall x, x \in (Plus a c) -> x \in r.
Proof.
move => a c ha hc r.
rewrite ssublPlus2; case/andP => h1 h2 x.
by rewrite -topredE /=; case/orP => hu;
    [ apply (ha r h1 x hu) | apply (hc r h2 x hu) ].
Qed.

Lemma ssubrPlus_ok : forall a c, 
  (forall b, ssubr a b -> forall x, x \in b -> x \in a) ->
  (forall d, ssubr c d -> forall x, x \in d -> x \in c) ->
  forall r, ssubr (Plus a c) r -> 
  forall x, x \in r -> x \in (Plus a c).
Proof.
move => a c ha hc r.
elim : r => [ | | |s  | d _ | c1 hc1 c2  hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | d _ ]; try (by
  rewrite ssubrPlus1 //; case/orP => hu x hx; 
    rewrite !inE; apply/orP; 
    [left; apply (ha _ hu) | right; apply (hc _ hu)]
  ).
- by rewrite ssubrPlus1.
rewrite ssubrPlus2; case/andP => h1 h2 x.
rewrite -topredE /=.
case/orP => hu.
- by apply: hc1.
by apply: hc2. 
Qed.

Lemma ssublAnd_ok : forall a c, 
  (forall b, ssubl a b -> forall x, x \in a -> x \in b) ->
  (forall d, ssubl c d -> forall x, x \in c -> x \in d) ->
  forall r, ssubl (And a c) r -> 
  forall x, x \in (And a c) -> x \in r.
Proof.
move => a c ha hc.
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- by rewrite ssublPlus1 => //;
    case/orP => hu x hx;  rewrite -topredE /=; 
     apply/orP; [left; rewrite (hd1 hu x hx) | 
                right; rewrite (hd2 hu x hx)].
rewrite ssublAnd; case/andP => h1 h2 x. rewrite -!topredE /=. 
case/andP => h3 h4. 
apply/andP. by rewrite (ha d1 h1 x h3) (hc d2 h2 x h4).
Qed.

Lemma ssubrAnd_ok : forall a c, 
  (forall b, ssubr a b -> forall x, x \in b -> x \in a) ->
  (forall d, ssubr c d -> forall x, x \in d -> x \in c) ->
  forall r, ssubr (And a c) r -> 
  forall x, x \in r -> x \in (And a c).
Proof.
move => a c ha hc.
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- rewrite ssubrPlus2. 
  case/andP => h1 h2 x.
  rewrite -topredE /=; case/orP => hu; 
    [ by apply hd1 | by apply hd2].
rewrite ssubrAnd; case/andP => h1 h2 x. rewrite -!topredE /=. 
case/andP => h3 h4. 
apply/andP. by rewrite (ha d1 h1 x h3) (hc d2 h2 x h4).
Qed.

Lemma ssublConc_ok : forall a c, 
  (forall b, ssubl a b -> forall x, x \in a -> x \in b) ->
  (forall d, ssubl c d -> forall x, x \in c -> x \in d) ->
  forall r, ssubl (Conc a c) r -> 
  forall x, x \in (Conc a c) -> x \in r.
Proof.
move => a c ha hc.
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- by rewrite ssublPlus1 => //;
    case/orP => hu x hx;  rewrite -topredE /=; 
     apply/orP; [left; rewrite (hd1 hu x hx) | 
                right; rewrite (hd2 hu x hx)].
rewrite ssublConc; case/andP => h1 h2 x. rewrite -!topredE /=. 
case/concP => u [v [hv [hu huv]]].
apply/concP; exists u.  
exists v; split => //; split; first by rewrite (ha d1 h1 u hu).
by rewrite (hc d2 h2 v huv).
Qed.

Lemma ssubrConc_ok : forall a c, 
  (forall b, ssubr a b -> forall x, x \in b -> x \in a) ->
  (forall d, ssubr c d -> forall x, x \in d -> x \in c) ->
  forall r, ssubr (Conc a c) r -> 
  forall x, x \in r -> x \in (Conc a c).
Proof.
move => a c ha hc.
elim => [ | | |t  | d _ | d1 hd1 d2 hd2 | 
  d1 _ d2 _ | d1 _ d2 _ | d _ ] //.
- rewrite ssubrPlus2. 
  case/andP => h1 h2 x.
  rewrite -topredE /=; case/orP => hu; 
    [ by apply hd1 | by apply hd2].
rewrite ssubrConc; case/andP => h1 h2 x. rewrite -!topredE /=. 
case/concP => u [v [hu [hv huv]]]. 
apply/concP; exists u.
exists v; split => //; split; first by rewrite (ha d1 h1 u hv).
by rewrite (hc d2 h2 v huv).
Qed.

Lemma ssublr_ok : forall a b, 
 (ssubl a b -> {subset a <= b}) /\ (ssubr a b -> {subset b <= a}).
Proof.
rewrite /sub_mem.
elim => [ | | |s  | c hc | c1 hc1 c2 hc2 | 
  c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc ] //.
- move => b; split.
  + move => _ x. by rewrite -topredE /=. 
  by apply ssubrVoid_ok. 
- move => b; split.
  + by apply ssublEps_ok.
  by apply ssubrEps_ok.
- move => b; split.
  + by apply ssublDot_ok.
  by apply ssubrDot_ok.
- move => b; split.
  + by apply ssublAtom_ok.
  by apply ssubrAtom_ok.
- have h1 : (forall b, ssubl c b -> forall x, x \in c -> x \in b) 
    by apply hc.
  have h2 : (forall b, ssubr c b -> forall x, x \in b -> x \in c) 
    by apply hc.
  clear hc; split.
  + by apply ssublStar_ok.
  by apply ssubrStar_ok.
- have h1 : (forall b, ssubl c1 b -> forall x, x \in c1 -> x \in b) 
    by apply hc1.
  have h2 : (forall b, ssubr c1 b -> forall x, x \in b -> x \in c1) 
    by apply hc1.
  have h3 : (forall b, ssubl c2 b -> forall x, x \in c2 -> x \in b) 
    by apply hc2.
  have h4 : (forall b, ssubr c2 b -> forall x, x \in b -> x \in c2) 
    by apply hc2.
  clear hc1 hc2; split.
  + by apply ssublPlus_ok. 
  by apply ssubrPlus_ok.
- have h1 : (forall b, ssubl c1 b -> forall x, x \in c1 -> x \in b) 
    by apply hc1.
  have h2 : (forall b, ssubr c1 b -> forall x, x \in b -> x \in c1) 
    by apply hc1.
  have h3 : (forall b, ssubl c2 b -> forall x, x \in c2 -> x \in b) 
    by apply hc2.
  have h4 : (forall b, ssubr c2 b -> forall x, x \in b -> x \in c2) 
    by apply hc2.
  clear hc1 hc2; split.
  + by apply ssublAnd_ok. 
  by apply ssubrAnd_ok.
- have h1 : (forall b, ssubl c1 b -> forall x, x \in c1 -> x \in b) 
    by apply hc1.
  have h2 : (forall b, ssubr c1 b -> forall x, x \in b -> x \in c1) 
    by apply hc1.
  have h3 : (forall b, ssubl c2 b -> forall x, x \in c2 -> x \in b) 
    by apply hc2.
  have h4 : (forall b, ssubr c2 b -> forall x, x \in b -> x \in c2) 
    by apply hc2.
  clear hc1 hc2; split.
  + by apply ssublConc_ok. 
  by apply ssubrConc_ok.
have h1 : (forall b, ssubl c b -> forall x, x \in c -> x \in b) 
  by apply hc.
have h2 : (forall b, ssubr c b -> forall x, x \in b -> x \in c) 
  by apply hc.
clear hc; split.
- by apply ssublNot_ok.
by apply ssubrNot_ok.
Qed.

Lemma ssim1_ok : forall r s, ssim1 r s -> r =i s.
Proof.
rewrite /ssim1 => r s.
case: (@ssublr_ok r s). rewrite /sub_mem => h1 h2.
case/andP.
move/h1 => hl; move/h2 => hr x.
apply/idP/idP.
- by apply: hl. 
by apply: hr.
Qed. 

Global Instance ssim1_Eq : Equivalence ssim1.
Proof.
split. 
- red. by apply ssim1_refl.
- red. by move => x y h; rewrite ssim1C.
red. rewrite /ssim1 => x y z.
case/andP => h1 h2; case/andP => h3 h4.  
apply/andP; split.
- by apply (@ssublr_trans y x z).
by apply (@ssublr_trans y x z).
Qed.

End Similarity1.

(**  Compatibility definitions to use in ex.v:
       - Der is inductivelty finite for sim1
       - sim1 enjoys Brzozowsky rewriting rules
       - sim1 preserves the associated language
*)
Definition sim1_finite_number_of_der :=
  finite_number_of_der 
  (@ssim1_Plus_id _) (@ssim1_PlusC _) (@ssim1_PlusA _)
  (@ssim1_congr_Conc _) (@ssim1_congr_Plus _) (@ssim1_congr_And _)
  (@ssim1_congr_Star _) (@ssim1_congr_Not [eqType of bool]).

Definition sim1_build_list_fun :=
  build_list_fun 
  (@ssim1_Plus_id _) (@ssim1_PlusC _) (@ssim1_PlusA _)
  (@ssim1_congr_Conc _) (@ssim1_congr_Plus _) (@ssim1_congr_And _)
  (@ssim1_congr_Star _) (@ssim1_congr_Not [eqType of bool]).

Definition sim1_build_list_der :=
 build_list_der
  (@ssim1_Plus_id _) (@ssim1_PlusC _) (@ssim1_PlusA _)
  (@ssim1_congr_Conc _) (@ssim1_congr_Plus _) (@ssim1_congr_And _)
  (@ssim1_congr_Star _) (@ssim1_congr_Not [eqType of bool]).

Definition sim1_bregexp_eq := 
  bregexp_eq
  (@ssim1_Plus_id _) (@ssim1_PlusC _) (@ssim1_PlusA _)
  (@ssim1_congr_Conc _) (@ssim1_congr_Plus _) (@ssim1_congr_And _)
  (@ssim1_congr_Star _) (@ssim1_congr_Not [eqType of bool]).

Definition sim1_bregexp_sub :=
 bregexp_sub
  (@ssim1_Plus_id _) (@ssim1_PlusC _) (@ssim1_PlusA _)
  (@ssim1_congr_Conc _) (@ssim1_congr_Plus _) (@ssim1_congr_And _)
  (@ssim1_congr_Star _) (@ssim1_congr_Not [eqType of bool]).
