(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
From RegLang Require Import languages.
From RegexpBrzozowski Require Import glue.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.
(* end hide*)

Section RegExp.
(** Character or symbol *)
Variable char : eqType.

(** Extended regular expression with boolean operators *)
Inductive regular_expression :=  
 | Void 
 | Eps
 | Dot  
 | Atom of char 
 | Star of regular_expression
 | Plus of regular_expression & regular_expression 
 | And of regular_expression & regular_expression
 | Conc of regular_expression & regular_expression
 | Not of regular_expression.

(* begin hide *)
Implicit Type e : regular_expression.
(* end hide *)
(** Add an eqType structure to regular_expression.
   Note: we will not use it in this file, only at the very
   end since the structural equality over regular_expression
   is not interesting in itself (e.g. it does not equal A and A + A *)
Fixpoint regexp_struct_eq (e1 e2: regular_expression) : bool :=
match e1,e2 with
 | Void, Void => true
 | Eps, Eps => true
 | Dot, Dot => true
 | Atom n, Atom p => n == p
 | Star e1, Star e2 => regexp_struct_eq e1 e2
 | Plus e1 e2, Plus f1 f2 => regexp_struct_eq e1 f1 && regexp_struct_eq e2 f2
 | And e1 e2, And f1 f2 => regexp_struct_eq e1 f1 && regexp_struct_eq e2 f2
 | Conc e1 e2, Conc f1 f2 => regexp_struct_eq e1 f1 && regexp_struct_eq e2 f2
 | Not e1, Not e2 => regexp_struct_eq e1 e2
 | _, _ => false
end.

Lemma regexp_struct_eq_refl : forall e, regexp_struct_eq e e.
Proof.
elim => [ | | | s | c hc | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc] //=;
  by apply/andP; split.
Qed.

Lemma regular_expression_eq_axiom : Equality.axiom regexp_struct_eq.
Proof.
move => r1 r2. apply: (iffP idP); [ | by move => ->; apply regexp_struct_eq_refl].
elim :r1 r2 => [ | | | s | c hc | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c hc] //=.
- by case.
- by case.
- by case.
- case => //=. by move => t heq; rewrite (eqP heq).
- case => //=. move => r hi; by rewrite (hc r hi).
- case => //=. move => r1 r2. case/andP => hi1 hi2. by rewrite (hc1 r1 hi1) (hc2 r2 hi2).
- case => //=. move => r1 r2. case/andP => hi1 hi2. by rewrite (hc1 r1 hi1) (hc2 r2 hi2).
- case => //=. move => r1 r2. case/andP => hi1 hi2. by rewrite (hc1 r1 hi1) (hc2 r2 hi2).
- case => //=. move => r hi; by rewrite (hc r hi).
Qed.

Definition regexp_eq_mixin := EqMixin regular_expression_eq_axiom.

Canonical Structure regexp_eqType := EqType regular_expression regexp_eq_mixin.

Local Arguments void : clear implicits.
Local Arguments eps : clear implicits.
Local Arguments dot : clear implicits.
                                                            
(** Function that translate a regexp into its associated language *)
Fixpoint mem_reg e := 
  match e with 
  | Void => void char
  | Eps => eps char
  | Dot => dot char
  | Atom x => atom x 
  | Star e1 => star (mem_reg e1) 
  | Plus e1 e2 => plus (mem_reg e1) (mem_reg e2) 
  | And e1 e2 => prod (mem_reg e1) (mem_reg e2)
  | Conc e1 e2 => conc (mem_reg e1) (mem_reg e2) 
  | Not e1 => compl (mem_reg e1)
  end. 

Canonical Structure req_exp_predType := PredType mem_reg.

(** The delta operator:
    Test to check whether the epsilon is part of a regexp *)
Fixpoint has_eps e := 
  match e with 
  | Void => false 
  | Eps => true
  | Dot => false 
  | Atom x => false 
  | Star e1 => true 
  | Plus e1 e2 => has_eps e1 || has_eps e2 
  | And e1 e2 => has_eps e1 && has_eps e2
  | Conc e1 e2 => has_eps e1 && has_eps e2 
  | Not e1 => ~~ (has_eps e1)
  end.

(** If a regexp contains epsilon, its language contains the empty word *)
Lemma has_epsE : forall e, has_eps e = ([::] \in e). 
Proof.
elim => //= [c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 hc1 ].
- by rewrite hc1 hc2. 
- by rewrite hc1 hc2.
- rewrite hc1 hc2 => //. rewrite -[xx in _ = xx] topredE /=. (* rewrite -[_ \in Conc _ _] topredE /=.*)
  by apply/idP/existsP; [exists ord0| case].
- by rewrite hc1.
Qed.

(** Derivate of a regexp e with respect to a letter x *)
Fixpoint der x e := 
  match e with 
  | Void => Void 
  | Eps => Void 
  | Dot => Eps
  | Atom y => if x == y then Eps else Void 
  | Star e1 => Conc (der x e1) (Star e1) 
  | Plus e1 e2 => Plus (der x e1) (der x e2)
  | And e1 e2 => And (der x e1) (der x e2)
  | Conc e1 e2 => if has_eps e1 then 
     Plus (Conc (der x e1) e2) (der x e2)
     else Conc (der x e1) e2
  | Not e1 => Not (der x e1)
  end. 

Lemma PlusVoid : forall c, c =i Plus c Void.
Proof.
move => c x.
rewrite -[_ \in Plus _ _]topredE /=.
apply/idP/orP; first by move => h; left.
by case.
Qed.

(** The operation of derivation is equivalent to the computation of residual *)

Lemma derE : forall x e, der x e =i residual x (mem e). 
Proof.
move=> x; elim=> //= [ | y | e IHe | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1] u. 
- rewrite -!topredE /=. apply/idP/idP => h. rewrite /eps !inE /= in h .
  by rewrite (eqP h) /=. rewrite /residual !inE /= in h. by case :u h.
- by rewrite 2!fun_if.  
- by apply/concP/concP=> [] [v e_v]; exists v; rewrite // IHe in e_v *. 
- by rewrite !inE IHe1 IHe2. 
- by rewrite !inE IHe1 IHe2.
- case he: (has_eps e1).
  + apply/orP/concP=> [[] | [[|y v]]] /=; rewrite -/mem_reg.
    * move/concP=> [w1 [w2 uw]].
      move: uw; rewrite IHe1 in_residual; move => [uw [w1e w2e]].
      by exists (x :: w1), w2; rewrite uw.
    * move => hu. exists [::]. rewrite -has_epsE.
      exists (x::u) => //. by rewrite -in_residual -IHe2.
    * case=> w [def_w [_ e2w]]; right.
      by rewrite IHe2 !inE def_w.
    * case=> w [[xy uvw] [e1w e2w]]; left; apply/concP.
      by exists v, w; rewrite IHe1 xy in_residual.
  + apply/concP/concP => [[v] | ] /=; rewrite -/mem_reg.
    case=> w [uw [e1w e2w]].
    exists (x :: v), w.
    by rewrite uw -in_residual -IHe1.
  + case; case => [|y v]; case => /= w [hv [he1 he2]].
      by move: he; rewrite has_epsE he1.
    move/eqP: hv.
    rewrite eqseq_cons. case/andP. 
    move/eqP => hx. move/eqP => hu. exists v. 
    by rewrite IHe1 in_residual hx; exists w.
- by rewrite -topredE /= /compl /= topredE IHe1.
Qed.

(** How to derivate by a word instead then just a letter *)
Fixpoint wder u e := if u is x :: v then wder v (der x e) else e.

Lemma wder_cat : forall s t E, wder (s++t) E = wder t (wder s E).
Proof.
elim => [ | hd tl hi] t E //=.
Qed.
(* end hide *)

(** This gives us a test to check whether a word is in a language:
 u is recognized by the regexp e if epsilon is recognized by der e u *)
Fixpoint mem_der e u := if u is x :: v then mem_der (der x e) v else has_eps e.
 
Lemma mem_derE : forall u e, mem_der e u = (u \in e). 
Proof. by elim=> [|x u IHu] e /=; rewrite ?has_epsE // IHu derE. Qed. 

Lemma mem_wder : forall s e, mem_der e s = has_eps (wder s e).
Proof.
by elim => /=.
Qed.

(** The language of all words is encoded as "not the empty language"
    but it can also be encoded as .*  *)
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

(** general shape of the derivatives by a _word_ *)
Lemma wder_Void : forall u, wder u Void = Void.
Proof.
by elim => [ | hd tl hi]  //=.
Qed.

Lemma wder_Plus: forall u E F, 
  wder u (Plus E F) = Plus (wder u E) (wder u F).
Proof.
by elim => [ | hd tl hi] E F  //=.
Qed. 

Lemma wder_And: forall u E F, wder u (And E F) = And (wder u E) (wder u F).
Proof.
by elim => [ | hd tl hi] E F //=.
Qed.

Lemma wder_Not : forall u E, wder u (Not E) = Not (wder u E).
Proof.
by elim => [ | hd tl hi] E //=.
Qed.

Lemma wder_Eps : forall u, wder u Eps = Eps \/ wder u Eps = Void.
Proof.
case => [ | hd tl] /=. by left. by right; rewrite wder_Void.
Qed.

Lemma wder_Dot : forall u,
 wder u Dot = Dot \/ wder u Dot = Eps \/ wder u Dot = Void.
Proof.
case => [ | hd ] /=. by left.
case => [ | hd' tl'] /=. by right; left.
by right; right ; apply wder_Void.
Qed.

Lemma wder_Atom : forall u n,
 wder u (Atom n) = Atom n \/  
 wder u (Atom n) = Eps \/ wder u (Atom n) = Void.
Proof.
case => [ | hd ] /=. move => n;  by left.
case => [ | hd' tl'] n /=. case : eq_op. by right; left. by right; right.
case: eq_op => /=; by right;right;  rewrite wder_Void.
Qed.


(** first issue: general form of derivative of Conc 
  (see Brozowsky for the litterate form)
 
 (EF)/s = (E/s)F + Sigma {  delta(E/t) F/u |   s = tu and u <> epsilon } 
  
  invariant : s ++ t constant *)
Fixpoint wder_sigma (r1 r2: regular_expression) (s t: word char) : 
  regular_expression :=
  match t with
  | [::] => Conc (wder s r1) r2
  | hd :: tl => if has_eps (wder s r1) then 
      Plus (wder_sigma r1 r2 (s ++ [:: hd]) tl) (wder t r2)
     else wder_sigma r1 r2 (s ++ [:: hd]) tl
end.

Lemma wder_sigma_switch : forall t s x E F, 
  wder_sigma (der x E) F s t = wder_sigma E F [:: x & s] t.
Proof.
elim => [ | hd tl hi] s x E F //=. case (has_eps (wder s (der x E))).
congr Plus. by rewrite hi. by rewrite hi.
Qed.

Lemma wder_Conc: forall u E F, wder u (Conc E F) = wder_sigma E F [::] u.
Proof.
elim => [ | hd tl hi] E F //=. case: (has_eps E).  
- by rewrite wder_Plus hi wder_sigma_switch.
by rewrite hi wder_sigma_switch.
Qed.

(** The generic form of derivatives of Star is pretty easy
   to write with ... but not formally, so I crush it
   by stating it up to similarity (see finite_der.v) 
   to be able to have any ordering on subterms.

   its main form is:
   (E* )/s = E/s.E* + \sigma_s \delta(E/s_1)...\delta(E/s_p)E/s_q.E*
   for any possibility to write s = s_1 ++ s_2 ++ .. ++ s_p ++ s_q
   with s_i <> [::]

  for example, (E* )/xy = E/xy.E* + \delta(E/x) E/y.E*
	       (E* )/xyz = E/xyz.E* + \delta(E/x) E/yz.E* +
	      	          \delta(E/x)\delta(E/y) E/z.E*  +
			  \delta(E/xy) E/z.E*
 
  to keep it simple, I just say that
  (E* )/[] = E* and (E* )/x::s = (E.E* )/s as we already know
  the form of (P.Q)/s
*) 

End RegExp.
