(* begin hide *)
From Coq Require Import RelationClasses Setoid Morphisms Permutation.
From Coq Require Import SetoidList Mergesort Orders.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
From RegLang Require Import languages.
From RegexpBrzozowski Require Import glue gfinset regexp.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits. 

(* end hide *)

Section FiniteDer.

(** the alphabet is style abstract *)
Variable symbol : eqType.

Let regexp := regular_expression symbol.
Let word := word symbol.

(** Specification of the similarity:
    we want a decidable relation ~ over regexp such that:
     - r1 ~ r2 -> L(r1) = L(r2)
     - A + A ~ A
     - A + B ~ B + A
     - A + (B + C) ~ (A + B) ~ C
     - ~ is a congruence for regexp
*)
Variable similar : regexp -> regexp -> bool. 
Context `{Equivalence regexp similar}.
Variable similar_ok : forall c1 c2, similar c1 c2 -> (c1 =i c2).
Variable similar_Plus_id : forall c, similar (Plus c c) c.
Variable similar_PlusC : forall c1 c2, similar (Plus c1 c2) (Plus c2 c1).
Variable similar_PlusA : forall c1 c2 c3, 
 similar (Plus (Plus c1 c2) c3) (Plus c1 (Plus c2 c3)).

Variable similar_congr_Conc : forall a b c d, similar a b -> similar c d ->
 similar (Conc a c) (Conc b d).
Variable similar_congr_Plus : forall a b c d, similar a b -> similar c d ->
 similar (Plus a c) (Plus b d).
Variable similar_congr_And : forall a b c d, similar a b -> similar c d ->
 similar (And a c) (And b d).
Variable similar_congr_Star : forall a b, 
  similar a b -> similar (Star a) (Star b).
Variable similar_congr_Not : forall a b, similar a b -> 
  similar (Not a) (Not b).

(** if r1 ~ r2 then delta r1 = delta r2 *)
Lemma has_eps_sim : forall r1 r2, similar r1 r2 -> has_eps r1 = has_eps r2.
Proof.
move => r1 r2.
move/similar_ok => h.
rewrite !has_epsE.
by rewrite (h [::]). 
Qed.

(* begin hide *)
Lemma similar_PlusAC : forall c1 c2 c3,  
 similar (Plus (Plus c1 c2) c3) (Plus (Plus c1 c3) c2).
Proof.
move => c1 c2 c3.
transitivity (Plus c1 (Plus c2 c3)); first by apply: similar_PlusA.
transitivity (Plus c1 (Plus c3 c2)).
- apply similar_congr_Plus; first reflexivity.
  by apply similar_PlusC.
symmetry; by apply : similar_PlusA.
Qed.
(* end hide *)
(** General form of the derivative of a star by a word, up to 
    similarity (see regexp.v for a detailed explanation) *)
Lemma wder_Star : forall u E, 
  similar (wder u (Star E)) (match u with
                               | [::] => Star E
                               | _ => wder_sigma E (Star E) nil u
                             end).
Proof.
elim => [ | hd tl hi] E //=. 
- reflexivity.
rewrite wder_Conc wder_sigma_switch.
case: (has_eps E). 
- by symmetry. 
reflexivity.
Qed.



(** Sets of derivatives of E with respect to the similarity *)
Definition set_of_der : grel regexp := fun E F =>
  exists s: word, similar F (wder s E).

(* reification of similar into Prop *)
Definition sim : grel regexp := fun c1 c2 => similar c1 c2.
Definition nsim :grel regexp := (@neq _)  similar . 


(**
    all our sets of derivative are compatible with similarity, 
   so we can use our gfinset developmment *)
Lemma set_of_der_compat : forall E x y, sim x y -> 
  set_of_der E x -> set_of_der E y.
Proof.
rewrite /set_of_der => E x y.
rewrite /sim => heq.
case => s heq2. exists s.  transitivity x => //. by symmetry. 
Qed.

(** Similarity is decidable *)
Lemma sim_dec : forall x y, {sim x y}+{~ sim x y}.
Proof.
move => x y. rewrite /sim.
case: (similar x y). by left. by right.
Defined.

Definition eqs := (@eql _) sim.
Definition neqs := neql sim.
Definition eqs_elim := eql_elim sim_dec.
Definition neqs_elim := neql_elim sim_dec.

Global Instance eqs_Eq : Equivalence eqs.
Proof.
split.
- move => l. apply/eqs_elim. by move => x; split.
- move => l l'. move/eqs_elim => h. apply eqs_elim.
  move => x; split => h'. case: (h x) => _ . by apply.  case: (h x) => h'' _ . by apply:h''.
- move => l l' l''. move/eqs_elim => h. move/eqs_elim => h'. apply/eqs_elim => x.
  case: (h x) => h1 h2. case: (h' x) => h3 h4. split => hx.
  by apply: h3; apply h1. by apply : h2;  apply h4.
Qed.


(** handy function to use with gfinset.Bar_fun to show that their image 
   are finite *)
Definition fPlus (EF : regexp * regexp) : regexp := 
 let (E,F) := EF in Plus E F.
Definition fAnd (EF : regexp * regexp) : regexp := 
 let (E,F) := EF in And E F.
Definition fNot (E : regexp) : regexp := Not E.
Definition fConc (EF : regexp * regexp) : regexp := 
 let (E,F) := EF in Conc E F.

(* Definition of some predicates *)
Definition pred_plus P Q : gset regexp := fun G => 
 exists E, exists F, P E /\  Q F /\ similar G (Plus E F).
Definition pred_and P Q : gset regexp := fun G => 
 exists E, exists F,  P E /\  Q F /\ similar G (And E F).
Definition pred_not P : gset regexp := fun G => 
 exists E,  P E /\ similar G (Not E).
Definition pred_conc P Q : gset regexp := fun G => 
 exists E, exists F,  P E /\  Q F /\  similar G (Conc E F).
Definition pred_singl P : gset regexp := fun G => similar G P.
Definition pred_scalar P F : gset regexp := fun G => 
 exists e,  P e /\ similar G (Conc e F).


Notation "'Finite' E" := (IFinite sim E) (at level 80). 

(** A singleton is a finite set *)
Lemma finite_pred_singl : forall P, Finite (pred_singl P).
Proof.
move => P. apply: cBar => G1. rewrite /In /pred_singl => h1. 
apply cBar => G2. case => []. move => h2.  case.  move: h1 h2. 
rewrite /sim. move => h1 h2.
transitivity P => //. by symmetry. 
Qed.

(** if a set P is finite, its product by a constant stays finite 
   "product" is concatenation of regexp *)
Lemma finite_pred_scalar : forall P F, 
  Finite P -> Finite (pred_scalar P F). 
Proof.
move => P F hdP.
have hsim : 
 Finite (@f_set (regexp*regexp) regexp sim fConc (Prod P (pred_singl F))).
- apply : (@Bar_fun _ _  (eq_prod sim sim)).
  + move => [a1 b1] [a2 b2]. case. rewrite /sim /fConc /=. 
    move => h1 h2.  by apply similar_congr_Conc. 
  apply : (@Bar_grel_incl _ _ (r_prod nsim nsim)).
  apply: Bar_gset_prod; first done. apply finite_pred_singl.
  move => [a1 b1] [a2 b2].  rewrite  /nsim /neq /eq_prod  /r_prod /sim.
  case: (similar a1 a2) => h. right.  move => h'. apply :h. by split.
  by left.
apply: (@Bar_gset_incl _  (f_set sim fConc (Prod  P (pred_singl  F)))); 
  first done. 
move => x. case. move => y [hl hr]. rewrite /f_set.
exists (y,F). split => //. rewrite /pred_singl. reflexivity.
rewrite /sim  /fConc. by symmetry. 
Qed.

(** A regexp is a derivative of (E+F) if it's of the shape
    e + f with e \in derivative E and f \in derivative F *) 
Lemma incl_der_pred_plus: forall E F, 
 Included (set_of_der (Plus E F)) (pred_plus (set_of_der E) (set_of_der F)).
Proof.
move => E F x. rewrite /In /set_of_der. case => u. rewrite wder_Plus. 
move=> h2.
rewrite /pred_plus.
- exists (wder u E); exists (wder u F); split. 
  exists u. reflexivity.
split => //.
by exists u; reflexivity. 
Qed.


Lemma finite_pred_plus : forall E F, Finite (set_of_der E) -> 
  Finite (set_of_der F) ->
  Finite (pred_plus (set_of_der E) (set_of_der F)).
Proof.
move => E F hE hF.
have hsim : Finite (@f_set (regexp*regexp) regexp sim fPlus 
  (Prod (set_of_der E) (set_of_der F))).
- apply:  (@Bar_fun _ _ (eq_prod sim sim)).
  + move => [a1 b1] [a2 b2]. case. rewrite /sim /fPlus /=. 
    move => h1 h2; by apply similar_congr_Plus. 
  apply : (@Bar_grel_incl _ _ (r_prod nsim nsim)). by apply: Bar_gset_prod.
  move => [a1 b1] [a2 b2].  rewrite  /nsim /neq /eq_prod /r_prod /sim.
  case: (similar a1 a2) => h. right. move => h'. apply :h. 
  by split. by left.
apply: (@Bar_gset_incl _ 
 (f_set sim fPlus (Prod (set_of_der E) (set_of_der F)))); first done.
move => x. rewrite /In /f_set /pred_plus. case. move => y.  move => [R []]. 
move =>  h1 [h2 h3]. exists (y,R).  by split. 
by symmetry. 
Qed.

(* if set_of_der E and set_of_der F are finite, 
   then set_of_der (E+F) is finite *)
Lemma finite_der_Plus : forall E F, Finite (set_of_der E) -> 
 Finite (set_of_der F) -> Finite (set_of_der (Plus E F)).
Proof.
move => E F hE hF.
apply: (@Bar_gset_incl  _ (pred_plus (set_of_der E) (set_of_der F))).
by apply : finite_pred_plus.
by apply: incl_der_pred_plus.
Qed.

(** Same evolution for And *)
Lemma incl_der_pred_and: forall E F, 
 Included (set_of_der (And E F)) (pred_and (set_of_der E) (set_of_der F)).
Proof.
move => E F x. rewrite /In /set_of_der. case => u. rewrite wder_And. 
move=> h2.
exists (wder u E); exists (wder u F); split.  by exists u; reflexivity. 
split => //. by exists u; reflexivity. 
Qed.

Lemma finite_pred_and : forall E F, Finite (set_of_der E) -> 
  Finite (set_of_der F) ->
  Finite (pred_and (set_of_der E) (set_of_der F)).
Proof.
move => E F hE hF.
have hsim : Finite (@f_set (regexp*regexp) regexp sim fAnd 
(Prod (set_of_der E) (set_of_der F))).
- apply:  (@Bar_fun _ _ (eq_prod sim sim)).
  + move => [a1 b1] [a2 b2]. case. rewrite /sim /fAnd /=. 
    move => h1 h2; by apply similar_congr_And. 
  apply : (@Bar_grel_incl _ _ (r_prod nsim nsim)). by apply: Bar_gset_prod.
  move => [a1 b1] [a2 b2].  rewrite  /nsim /neq /eq_prod /r_prod /sim.
  case: (similar a1 a2) => h. right. move => h'. apply :h. by split. 
  by left.
apply: (@Bar_gset_incl  _ 
 (f_set sim fAnd (Prod (set_of_der E) (set_of_der F)))); first done.
move => x. rewrite /In /f_set /pred_and. case. move => y.  
move => [R []].  move =>  h1 [h2 h3]. exists (y,R).  by split. 
by symmetry. 
Qed.

Lemma finite_der_And : forall E F, Finite (set_of_der E) -> 
  Finite (set_of_der F) -> Finite (set_of_der (And E F)).
Proof.
move => E F hE hF.
apply: (@Bar_gset_incl _ (pred_and (set_of_der E) (set_of_der F))).
by apply : finite_pred_and.
by apply: incl_der_pred_and.
Qed.

(* Same evolution for Not *)
Lemma incl_der_pred_not : forall E, 
 Included (set_of_der (Not E)) (pred_not (set_of_der E)).
Proof.
move => E x. rewrite /set_of_der. case => u. rewrite wder_Not. move=> h2.
exists (wder u E); split => //. by exists u; reflexivity. 
Qed.


Lemma finite_pred_not : forall E, Finite (set_of_der E) -> 
 Finite (pred_not (set_of_der E)).
Proof.
move => E hE.
have hsim : Finite (@f_set regexp regexp sim fNot (set_of_der E)).
- apply: (@Bar_fun _ _ sim); last done.
  move => a a'; rewrite /sim /fNot /= => h. by apply similar_congr_Not. 
apply: (@Bar_gset_incl _ (@f_set regexp regexp sim fNot (set_of_der E))); 
 first done.
move => x. rewrite /pred_not. case. move => y [h1 h2].
exists y => //. by symmetry. 
Qed.

Lemma finite_der_Not : forall E, Finite (set_of_der E) -> 
 Finite (set_of_der (Not E)).
Proof.
move => E hE.
apply: (@Bar_gset_incl _ (pred_not (set_of_der E))).
by apply: finite_pred_not.
by apply: incl_der_pred_not.
Qed.


(** Evolution for Plus and Star: a bit trickier *)

(** this function takes a list of regexp and an element
   and glue them together with Plus:
   rPlus a l == a + l1 + l2 + .. + ln
*)
Fixpoint rPlus a (l: seq regexp) := match l with
 | nil => a
 | hd :: tl => Plus (rPlus a tl) hd
end.


Definition set_of_der_conc (E F: regexp): gset regexp := 
 fun G => exists e, exists l, 
  (set_of_der E) e /\ gpred_list (set_of_der F) l /\ 
   similar G (rPlus (Conc e F) l).

Lemma rPlus_congr : forall l c1 c2, similar c1 c2 -> 
  similar (rPlus c1 l) (rPlus c2 l).
Proof.
elim => [ | hd tl hi] //= c1 c2 heq. 
apply similar_congr_Plus; last reflexivity.
by apply: hi. 
Qed.

Lemma incl_der_pred_conc : forall E F, 
 Included (set_of_der (Conc E F)) (set_of_der_conc E F).
Proof.
move => E F G. case => s.
rewrite wder_Conc. elim: s E F G => [ | hd tl hi] E F G /=.
- move => h. exists E; exists nil => /= ; split. 
  + by exists nil; reflexivity. 
  by split. 
case : (has_eps E).
- rewrite -wder_sigma_switch. 
  case: (@hi (der hd E) F (wder_sigma (der hd E) F [::] tl)). 
  + reflexivity. 
  move => G' [l ].  case => [[s hs] [h1 h2]] hG. exists (wder (hd::s) E).
  exists (cons (wder (hd::tl) F) l); split. 
  + exists (hd::s); by reflexivity.
  split => /=.
  + split => //.  exists (hd::tl); by reflexivity. 
  transitivity  
    (Plus (wder_sigma (der hd E) F [::] tl) (wder tl (der hd F))) => //.
  apply similar_congr_Plus; last reflexivity.
  transitivity (rPlus (Conc G' F) l) => //. 
  apply rPlus_congr. apply similar_congr_Conc; [ done | reflexivity].  
rewrite -wder_sigma_switch. 
case: (@hi (der hd E) F (wder_sigma (der hd E) F [::] tl)).  
- reflexivity.
move => G' [l].  case => [[s hs] [h1 h2]] hG. 
exists (wder (hd::s) E). exists l; split. 
- exists (hd::s); reflexivity. 
split => //=. 
transitivity (wder_sigma (der hd E) F [::] tl) => //.
transitivity (rPlus (Conc G' F) l) => //.  
apply rPlus_congr. 
apply similar_congr_Conc ; [ done | reflexivity].
Qed.

(** this function takes a list of regexp and two element, 
    and glue them together this way:

    rPlus2 (a.E* ) E* l = (a.E* )+(l1.E* )+....+(ln.E* )
*)


Definition rPlus2 a E l := rPlus a (map (fun x => Conc x E) l).

Lemma rPlus2_congr : forall l c1 c2 e1 e2, similar c1 c2 -> 
  similar e1 e2 -> similar (rPlus2 c1 e1 l) (rPlus2 c2 e2 l).
Proof.
rewrite /rPlus2 => l c1 c2 e1 e2 h1 h2.
elim: l => [ | hd tl hi] //=.
apply similar_congr_Plus. 
- by apply hi. 
by apply similar_congr_Conc; [reflexivity | done ]. 
Qed.

(* how to concat two rPlus2 *)
Lemma rPlus2_cat : forall l1 l2 a1 a2 E,
 similar (Plus (rPlus2 (Conc a1 E) E l1) (rPlus2 (Conc a2 E) E l2)) 
         (rPlus2 (Conc a2 E) E (a1::l1++l2)).
rewrite /rPlus2. elim => [ | hd tl hi] l2 a1 a2 E //=.
transitivity  
 (Plus (Plus (rPlus (Conc a1 E) (map (fun x => Conc x E) tl)) 
             (rPlus (Conc a2 E ) (map (fun x => Conc x E) l2))) 
       (Conc hd E)); 
 first (by apply: similar_PlusAC).
transitivity
 (Plus (rPlus (Conc a2 E) (map (fun x => Conc x E) (a1:: tl ++ l2)))
       (Conc hd E)) => /=.
- apply similar_congr_Plus; last by reflexivity. 
  by apply hi.
symmetry; by apply similar_PlusAC.
Qed.


Definition set_of_der_star (E:regexp) : gset regexp := fun G =>
 exists e, exists l,  (set_of_der E) e /\ gpred_list (set_of_der E) l /\ 
   similar G (rPlus2 (Conc e (Star E)) (Star E) l).

(** 
The main lemma to prove that (set_of_der E* ) \subset (set_of_der_star E) 
*)
Lemma incl_star_tool: forall tl hd E F u, 
  similar F (wder_sigma (wder u E) (Star E) [::] (hd :: tl)) ->
  exists e : regexp, exists l : seq regexp,
    set_of_der E e /\
    gpred_list (set_of_der E) l /\
    similar F (rPlus2 (Conc e (Star E)) (Star E) l).
Proof.
elim => [ | hd2 tl hi] hd E F u /=.
- case he: (has_eps (wder u E)) => /=.
  + move => hsim.
    exists (wder (u++[::hd]) E); exists [:: (der hd E)]; split => /=.
    * exists (u ++ [:: hd]); reflexivity. 
    split => /=. 
    * split => //=.
      by exists [:: hd]; reflexivity.  
   by rewrite wder_cat => /=.
  move => hsim. 
  exists (wder (u++[::hd]) E); exists [::]; split => //=.
  + exists (u++ [::hd]); reflexivity. 
  split => //.
  by rewrite wder_cat => /=.
case: (hi hd2 E 
 (wder_sigma (wder [::hd] E) (Star E) [::] (hd2::tl)) [::hd]) 
 => //= [  | e1 [l1 [hder1 [hpred1]]]].
- reflexivity.
case: (hi hd2 E (wder_sigma (wder (u++[::hd]) E) (Star E) [::] (hd2::tl))
  (u++[::hd])) => //= [ | e2 [l2 [hder2 [hpred2]]]].
- reflexivity.  
rewrite !wder_cat.
case : (has_eps (wder u E)); case: (has_eps (der hd (wder u E))); 
  case: (has_eps (der hd E)).
- rewrite -!wder_sigma_switch !wder_Plus !wder_Conc /=. 
  move => hsim2 hsim1. exists e1; exists (e2::l2++l1); split => //.
  split => /=. 
  + split => //. by apply  gpred_list_cat.
  transitivity (Plus
     (Plus (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
           (wder_sigma (der hd2 E) (Star E) [::] tl))
     (Plus (wder_sigma (der hd2 (der hd E)) (Star E) [::] tl)
           (wder_sigma (der hd2 E) (Star E) [::] tl))) => //.
  transitivity  (Plus (rPlus2 (Conc e2 (Star E)) (Star E) l2) 
                      (rPlus2 (Conc e1 (Star E)) (Star E) l1)).
  + by apply similar_congr_Plus.  
  by apply rPlus2_cat.
- rewrite -!wder_sigma_switch !wder_Conc /=.
  move => hsim2 hsim1 hF. exists e1; exists (e2::l2++l1); split => //.
  split => /=. 
  + split => //. by apply  gpred_list_cat.
  transitivity (Plus
     (Plus (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
           (wder_sigma (der hd2 E) (Star E) [::] tl))
     (wder_sigma (der hd2 (der hd E)) (Star E) [::] tl)) => //.
  transitivity (Plus (rPlus2 (Conc e2 (Star E)) (Star E) l2) 
                     (rPlus2 (Conc e1 (Star E)) (Star E) l1)).
  + by apply similar_congr_Plus.
  by apply rPlus2_cat.
- rewrite -!wder_sigma_switch !wder_Plus !wder_Conc /=.
  move => hsim2 hsim1 hF. exists e1; exists (e2::l2++l1); split => //.
  split => /=. 
  + split => //. by apply  gpred_list_cat.
  transitivity (Plus 
    (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
    (Plus (wder_sigma (der hd2 (der hd E)) (Star E) [::] tl)
          (wder_sigma (der hd2 E) (Star E) [::] tl))) => //.
  transitivity (Plus (rPlus2 (Conc e2 (Star E)) (Star E) l2) 
                     (rPlus2 (Conc e1 (Star E)) (Star E) l1)).   
  + by apply similar_congr_Plus.
  by apply rPlus2_cat.
- rewrite -!wder_sigma_switch !wder_Conc /=.
  move => hsim2 hsim1 hF. exists e1; exists (e2::l2++l1); split => //.
  split => /=. 
  + split => //. by apply  gpred_list_cat.
  transitivity (Plus 
    (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
    (wder_sigma (der hd2 (der hd E)) (Star E) [::] tl)) => //.
  transitivity (Plus (rPlus2 (Conc e2 (Star E)) (Star E) l2) 
                     (rPlus2 (Conc e1 (Star E)) (Star E) l1)).
  + by apply similar_congr_Plus.
  by apply rPlus2_cat.
- rewrite -!wder_sigma_switch !wder_Conc /=.
  move => hsim2 _ hf. exists e2; exists l2; split => //.
  split => //.
  by transitivity (Plus 
      (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
      (wder_sigma (der hd2 E) (Star E) [::] tl)) => //.
- rewrite -!wder_sigma_switch !wder_Conc  /=.
  move => hsim2 _ hF. exists e2; exists l2; split => //.
  split => //.
  by transitivity (Plus 
      (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl)
      (wder_sigma (der hd2 E) (Star E) [::] tl)).
- rewrite -!wder_sigma_switch !wder_Conc  /=.
  move => hsim2 _ hF. exists e2; exists l2; split => //.
  split => //.
  by transitivity 
      (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl).
rewrite -!wder_sigma_switch /=.
move => hsim2 hF. exists e2; exists l2; split => //.
split => //.
by transitivity (wder_sigma (der hd2 (der hd (wder u E))) (Star E) [::] tl).
Qed.

(** An element of set_of_der (E * ) is either E* or an element 
   of set_of_der_star E *)
Lemma incl_der_pred_star : forall E, 
  Included (set_of_der (Star E)) (Union (pred_singl (Star E))
           (set_of_der_star E )).
Proof.
move => E F. case => [] s /=. move: (wder_Star s E). 
case : s => [ | hd tl]. 
- move => h1 heq. left. rewrite /pred_singl. 
  by transitivity (wder [::] (Star E)).
move => h1 heq; right. apply : (@incl_star_tool tl hd E F [::]).
by transitivity (wder (hd :: tl) (Star E)).
Qed.

(** if e and l are derivatives of some E, than fConc2 (e,F,l) is
    a derivative of (Conc E F) *)
Definition fConc2 (args: regexp * regexp * seq regexp) : regexp := 
  let (eF,l) := args in let (e,F) := eF in rPlus (Conc e F) l.  

(** if e and l are derivatives of some E, then fStar (e,E,l) is
    a derivative of (E * ) *)
Definition fStar (args: regexp * regexp* seq regexp) : regexp :=
  let (eF,l) := args in let (e,F) := eF in 
  rPlus2 (Conc e (Star F)) (Star F) l.


(** inclusion of regular expression *)
Definition reg_incl r1 r2 := similar (Plus r1 r2) r2.

Definition lreg_incl (l1 l2 : seq regexp) := 
  all ( fun x => has (reg_incl x) l2  ) l1.


Lemma lreg_inclP : forall l1 l2, reflect 
 (forall x, (x \in l1) -> exists2 y, (y \in l2) & reg_incl x y)
 (lreg_incl l1 l2).
Proof.
rewrite /lreg_incl => l1 l2.
apply: (iffP idP).
- move/allP => ha x hx.
  by move/hasP : (ha x hx).
move => h.
apply/allP => x hx.  
apply/hasP.
by apply: h.
Qed.

Lemma lreg_incl1 : forall r l, reg_incl r (rPlus r l).
Proof.
rewrite /reg_incl => r. elim => [ | hd tl hi] //=.
transitivity (Plus (Plus r (rPlus r tl)) hd).
- by symmetry; apply similar_PlusA.
by apply similar_congr_Plus ; last reflexivity.
Qed.

Lemma reg_incl_Plus : forall r1 r2 r3, 
 (reg_incl r1 r3 && reg_incl r2 r3) -> reg_incl (Plus r1 r2) r3.
Proof.
rewrite /reg_incl => r1 r2 r3.
case/andP => h1 h2.
transitivity (Plus (Plus r1 r3) r2); first by apply similar_PlusAC.
transitivity (Plus r3 r2).
+ by apply similar_congr_Plus; last reflexivity.
by transitivity (Plus r2 r3); first apply similar_PlusC.
Qed.

Lemma reg_incl_Pl : forall r1 r2 r3, 
  reg_incl r1 r2 -> reg_incl r1 (Plus r2 r3).
Proof.
rewrite /reg_incl => r1 r2 r3 h.
transitivity (Plus (Plus r1 r2) r3); 
 first by symmetry; apply similar_PlusA.
transitivity (Plus r2 r3); last by reflexivity.
by apply similar_congr_Plus; last reflexivity.

Qed.

Lemma reg_incl_Pr : forall r1 r2 r3, 
  reg_incl r1 r2 -> reg_incl r1 (Plus r3 r2).
Proof.
rewrite /reg_incl => r1 r2 r3 h.
transitivity (Plus (Plus r1 r3) r2); 
 first by symmetry; apply similar_PlusA.
transitivity (Plus (Plus r1 r2) r3); first by apply similar_PlusAC.
transitivity (Plus r2 r3) => //.
by apply similar_congr_Plus; last reflexivity.
Qed.

Lemma reg_incl_has : forall x l, has (reg_incl x) l ->
 forall r, reg_incl x (rPlus r l).
Proof.
move => x.
elim => [ | hd tl hi] //=.
case/orP => hu r.
- by apply reg_incl_Pr.
by apply reg_incl_Pl; apply: hi.
Qed.

(* l \in_sim l' ->  rPlus l \in_sim rPlus l' *)
Lemma lreg_incl_reg : forall l1 l2, lreg_incl l1 l2 ->
  forall r, reg_incl (rPlus r l1) (rPlus r l2).
Proof.
elim => [ | hd tl hi] l2 //=.
- move => _ r; by apply : lreg_incl1.
case/andP => h1 h2 r.
apply reg_incl_Plus.
rewrite (hi l2 h2 r) /=.
by apply reg_incl_has.
Qed.

Lemma reg_incl_sim : forall r1 r2, 
 reg_incl r1 r2 && reg_incl r2 r1 =  similar r1 r2.
Proof.
rewrite /reg_incl => r1 r2.
apply/andP/idP.
- case => h1 h2.
  transitivity (Plus r1 r2) => //.
  symmetry; by transitivity (Plus r2 r1). 
move => h; split.
- transitivity (Plus r2 r2) => //.  
  by apply similar_congr_Plus; last reflexivity.
transitivity (Plus r1 r1) => //.
by apply similar_congr_Plus; [symmetry | reflexivity].
Qed.

Lemma lreg_incl_eqs : forall l1 l2, eqs l1 l2 ->
  (lreg_incl l1 l2 && lreg_incl l2 l1).
Proof.
move => l1 l2.
move/eqs_elim => h. 
apply/andP; split.
- apply/lreg_inclP => x hx.
  case: (@InA_inv _ _ _ sim_dec l2 x _) => [ | y h1 h2].
  + apply h. clear h.
    elim : l1 hx => [ | hd tl hi] //=.
    rewrite in_cons. case/orP => hu.
    * case: (sim_dec x hd) => //=.
      rewrite (eqP hu). case; reflexivity.
      rewrite (hi hu); by case: (sim_dec x hd).
  exists y => //.
  rewrite /reg_incl.
  transitivity (Plus y y) => //.
  by symmetry; apply similar_congr_Plus; last reflexivity.
- apply/lreg_inclP => x hx.
  case: (@InA_inv _ _ _ sim_dec l1 x _) => [ | y h1 h2].
  + apply h. clear h.
    elim : l2 hx => [ | hd tl hi] //=.
    rewrite in_cons. case/orP => hu.
    * case: (sim_dec x hd) => //=.
      rewrite (eqP hu). case; reflexivity.
      rewrite (hi hu); by case: (sim_dec x hd).
  exists y => //.
  rewrite /reg_incl.
  transitivity (Plus y y) => //.
  by symmetry; apply similar_congr_Plus; last reflexivity.
Qed.

(** definition of an equality over regexp * regexp * [regexp]
    that will be used as the  "eqB" equality later on to prove
    that the derivatives of Conc are finite *)
Definition eqtemp : grel (regexp * regexp * seq regexp) := 
  eq_prod (eq_prod sim sim) eqs. 

(** Major result: fConc2 and fStar are compatible with sim / eqtemp
    so we can use the gfinset.Bar_fun lemma *)
Lemma fConc2_compat : forall a a' : regexp * regexp * seq regexp, 
  eqtemp a a' -> similar (fConc2 a) (fConc2 a').
Proof.
case => [[e f] l] [[e' f'] l'].  rewrite /eqtemp /eq_prod /fConc2. 
rewrite /sim /= => [[[he1 he2]]].
move/lreg_incl_eqs.
case/andP.
move/lreg_incl_reg => h1.
move/lreg_incl_reg => h2.
transitivity (rPlus (Conc e f) l').
- by rewrite -reg_incl_sim (h1 (Conc e f)) (h2 (Conc e f)).
apply rPlus_congr.
by apply similar_congr_Conc.
Qed.

(* begin hide *)
Lemma map_InA : forall (x:regexp) f l, InA sim_dec (map f l) x ->
  exists2 y, similar x (f y) & InA sim_dec l y.
Proof.
move => x f; elim => [ | hd tl hi] //=.
case: (sim_dec x (f hd)) => //=.
- rewrite /sim => h _; exists hd => //.
  case: sim_dec => //=.
  case; reflexivity.
move => _ h; case : (hi h) => y  h1 h2.
exists y => //.
rewrite h2; by case: sim_dec.
Qed.

Lemma InA_map : forall (x:regexp) f,
 (forall x y, similar x y -> similar (f x) (f y)) ->
 forall l,
 InA sim_dec l x -> InA sim_dec (map f l) (f x). 
Proof.
move => x f hf. elim => [ | hd tl hi] => //=.
case: (sim_dec x hd) => hsim //=.
- move => _; case: sim_dec => //=.
  case. by apply: hf. 
move => h; rewrite (hi h).
by case: (sim_dec).
Qed.


Lemma eqs_mapE : forall E l l', eqs l l' -> 
  eqs (map (fun x => Conc x E) l) (map (fun x => Conc x E) l' ).
Proof.
move => E l l'; move/eqs_elim => h. apply/eqs_elim => x.
split.
- case/map_InA => y h1 h2.
  rewrite (InA_eq sim_dec _ h1). 
  apply: InA_map => //.
  + by move => a b hs; apply similar_congr_Conc; last reflexivity.
  by apply h.
- case/map_InA => y h1 h2.
  rewrite (InA_eq sim_dec _ h1). 
  apply: InA_map => //.
  + by move => a b hs; apply similar_congr_Conc; last reflexivity.
  by apply h.
Qed.
(* end hide *)

Lemma fStar_compat : forall a a' : regexp * regexp * seq regexp, 
  eqtemp a a' -> similar (fStar a) (fStar a').
Proof.
case => [[e f] l] [[e' f'] l'].  rewrite /eqtemp /eq_prod /fStar /rPlus2. 
rewrite /sim  => /= [[[he1 he2]]].
move/(eqs_mapE (Star f)). move/lreg_incl_eqs.
case/andP.
move/lreg_incl_reg => h1.
move/lreg_incl_reg => h2.
transitivity (rPlus (Conc e (Star f)) (map (fun x => Conc x (Star f)) l')).
- by rewrite -reg_incl_sim (h1 (Conc e (Star f)))  (h2 (Conc e (Star f))).
apply rPlus2_congr.
- apply similar_congr_Conc => //.
  by apply similar_congr_Star.
by apply similar_congr_Star.
Qed.


(* 
some inclusion properties we will need to use Bar_gpred_list and Bar_fun
*)
Lemma fpred_conc_incl : r_incl (neq eqtemp)
  (r_prod (r_prod nsim nsim) neqs).
case => [[e f] l] [[e' f'] l'].  
rewrite /nsim /neq /eqtemp /eq_prod /r_prod => hneq.
case: (sim_dec e e') => he. case: (sim_dec f f') => hf.
- right. apply : n_eql2neql. 
  + by apply sim_dec. 
  move => hl; apply: hneq. by split.
- by left; right.
by left; left.
Qed.


(** Proof that if (set_of_der E) and (set_of_der F) are finite, then
    (set_of_der_conc E F) is finite. Since set_of_der (Conc E F) is
    included inside the later, it is also finite
*)
Lemma finite_pred_der_conc : forall E F, 
 Finite (set_of_der E) -> Finite (set_of_der F) ->
 Finite (set_of_der_conc E F).
Proof.
move => E F hE hF.
(**
   first, we prove that fConc2 (set_of_der E, pred_singl F, gpred_list E) is
   finite by using the Bar_fun lemma.
*)
have hsim : Finite (@f_set (regexp*regexp*seq regexp) regexp sim fConc2
    (Prod (Prod (set_of_der E) (pred_singl F)) 
          (gpred_list (set_of_der F)))).
- apply: (@Bar_fun _ _ eqtemp).
  + by apply: fConc2_compat.
  apply : (@Bar_grel_incl _ _ (r_prod (r_prod nsim nsim) neqs)).  
  + apply :  Bar_gset_prod. 
    * apply: Bar_gset_prod; first done.
      by apply : finite_pred_singl.
    apply (@Bar_grel_incl _ _ (neq (eql sim))).
    * apply : Bar_gpred_list; last done.
        by apply: sim_dec.
      rewrite /E_compat. 
      by apply set_of_der_compat. 
    move => x y; apply : neql2n_eql.
    by apply: sim_dec.
  by apply: fpred_conc_incl.
(** then we show that the image of fCons2 is included (in fact it's equal)
   to set_of_der_conc *)
apply: (@Bar_gset_incl _ (f_set sim fConc2
              (Prod (Prod (set_of_der E) (pred_singl F))
                 (gpred_list (set_of_der F))))); first done.
move => x. case. move => y. move => [R [h1 [h2 h3]]].
rewrite /f_set. exists (y,F,R). split => //. split => //. 
rewrite /pred_singl; reflexivity.
rewrite /sim /fConc2.  by symmetry. 
Qed.


(** Same proof for set_of_der_star *)
Lemma finite_pred_der_star : forall E, Finite (set_of_der E) -> 
 Finite (set_of_der_star E ).
Proof.
move => E hE.
have hsim : Finite (@f_set (regexp*regexp*seq regexp) regexp sim fStar
    (Prod (Prod (set_of_der E) (pred_singl E)) 
          (gpred_list (set_of_der E)))).
- apply: (@Bar_fun _ _ eqtemp). 
  + by apply: fStar_compat.
  apply:  (@Bar_grel_incl _ _ (r_prod (r_prod nsim nsim) neqs)).
  + apply :  Bar_gset_prod. 
    * apply: Bar_gset_prod; first done. 
      by apply : finite_pred_singl.
    apply (@Bar_grel_incl _ _ (neq (eql sim))).
    * apply:  Bar_gpred_list; last done.
        by apply: sim_dec.
      rewrite /E_compat. 
      by apply set_of_der_compat. 
    move => x y; apply : neql2n_eql.
    by apply: sim_dec.
  by apply: fpred_conc_incl.
apply: (@Bar_gset_incl _ (f_set sim fStar
              (Prod (Prod (set_of_der E) (pred_singl E))
                 (gpred_list (set_of_der E))))); first done.
move => x. rewrite /set_of_der_star. case => e [l [h1 [h2 h3]]].
rewrite /f_set. exists (e,E,l). split => //. split => //.
by rewrite /pred_singl; reflexivity.
move :h3; rewrite /sim /fStar. by symmetry. 
Qed.

Lemma finite_der_Conc : forall E F, Finite (set_of_der E) -> 
  Finite (set_of_der F) -> 
  Finite (set_of_der (Conc E F)).
Proof.
move => E F hE hF.
apply: (@Bar_gset_incl _ (set_of_der_conc E F)).
by apply: finite_pred_der_conc.
by apply: incl_der_pred_conc.
Qed.

Lemma finite_der_Star : forall E, Finite (set_of_der E) -> 
 Finite (set_of_der (Star E)).
Proof.
move => E hE. 
apply: 
 (@Bar_gset_incl _ (Union (pred_singl (Star E)) (set_of_der_star E))).
apply: Bar_gset_union. by apply finite_pred_singl.
by apply: finite_pred_der_star.
by apply: incl_der_pred_star.
Qed.


(** Final result: the set of derivative of a regexp is finite. *)
(*
    The first cases are pretty hawfull because of our definition
    of finite: e.g. to check that set_of_der Dot is finite, we
    need to extract all of its element (which are limited to
    Eps Dot and Void), but we don't know the order or anything
    so we have to do all the possible combinaisons and 
    stop when we extract the same element twice.
*)
Lemma finite_number_of_der: forall e,  Finite  (set_of_der e).
Proof.
elim => [ | | | s | c1 hc1 | c1 hc1 c2 hc2 
  | c1 hc1 c2 hc2 | c1 hc1 c2 hc2 | c1 ] /=.
(* only Void is in wder Void *)
- apply: cBar => c. case => [ss]. 
  rewrite wder_Void /sim  => hVoid. apply cBar => [x]. case. case => [tt].
  rewrite wder_Void /sim  => hVoid2. case. rewrite /sim .
  transitivity (Void symbol) => //. by symmetry. 
(* only Eps or Void in is wder Eps *)
- apply: cBar => c. case => [ss]. 
  case : (wder_Eps ss) => ->.
  * move => hsim. apply cBar =>  [x].
    case. case => [ tt ]. case: (wder_Eps tt) => ->.
    + move => hsim2. case. rewrite /sim . 
      transitivity (Eps symbol) => //; by symmetry. 
    + move => hsim2 _. apply cBar => [x']. case => [] [[tt']].
      case: (wder_Eps tt') => ->; move => hsim3.
      case. transitivity (Eps symbol) =>//; by symmetry.
      move => _; case. transitivity (Void symbol) =>//; by symmetry.
  * move => hsim1. apply cBar =>  [x]. 
    case. case => [ tt ]. case: (wder_Eps tt) => ->.
    + move => hsim2 _ . apply cBar => [x']. case => [] [[tt']].
      case: (wder_Eps tt') => ->; move => hsim3. move => _; case.
      transitivity (Eps symbol) => //. by symmetry.
      case. transitivity (Void symbol) => //. by symmetry.
    + move => hsim2. case. transitivity (Void symbol) => //. by symmetry. 
(* same case study for Dot: only Eps Dot or Void are in wder Dot *)
- apply: cBar => c; case => [ss]. 
  case : (wder_Dot ss) => [ -> | [ -> | ->]]. 
  * move => h1. apply cBar =>  [x]. case.  case => [tt]. 
    case : (wder_Dot tt) => [ -> | [ -> | -> ]]. move => h2.
    + case. transitivity (Dot symbol) => //; by symmetry. 
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3. case.  by transitivity (Dot symbol) => //; symmetry. 
      move => h3 _. case. by transitivity (Eps symbol) => //; symmetry. 
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4. case. by transitivity (Dot symbol) =>//; symmetry. 
      move => h4 _ . case. by transitivity (Eps symbol) => //; symmetry. 
      move => h4 _ _ . case. by transitivity (Void symbol) =>//; symmetry. 
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3. case. by transitivity (Dot symbol) =>//; symmetry. 
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h4 _ _ . case. by transitivity (Eps symbol) => //; symmetry. 
      move => h4 _ . case. by transitivity (Void symbol) => //; symmetry. 
      move => h3 _. case.  by transitivity (Void symbol) => //; symmetry. 
  * move => h1; apply cBar =>  [x]. case.  case => [tt].
    case : (wder_Dot tt) => [ -> | [ -> | -> ]]. move => h2.
    + move =>  _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3 _. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h3. case.  by transitivity (Eps symbol) => //; symmetry. 
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4 _. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h4 . case. by transitivity (Eps symbol) =>//; symmetry. 
      move => h4 _ _ . case. by transitivity (Void symbol)=>//; symmetry. 
    + move => h2. case. by transitivity (Eps symbol) => //; symmetry. 
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4 _ _. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h4 . case.  by transitivity (Eps symbol) => //; symmetry. 
      move => h4 _ . case.  by transitivity (Void symbol) => //; symmetry. 
      move => h3. case.  by transitivity (Eps symbol) => //; symmetry. 
      move => h3 _. case.  by transitivity (Void symbol) => //; symmetry. 
  * move => h1; apply cBar =>  [x]. case.  case => [tt]. 
    case : (wder_Dot tt) => [ -> | [ -> | -> ]]. move => h2.
    + move =>  _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3 _. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4 _. case. by transitivity (Dot symbol) => //; symmetry. 
      move => h4 _ _ . case. by transitivity (Eps symbol) => //; symmetry. 
      move => h4 . case. by transitivity (Void symbol) => //; symmetry. 
      move => h3. case. by transitivity (Void symbol) => //; symmetry.
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Dot uu) => [ -> | [ -> | -> ]].
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Dot vv) => [ -> | [ -> | -> ]].
      move => h4 _ _. case. by transitivity (Dot symbol) => //; symmetry.
      move => h4 _ . case. by transitivity (Eps symbol) => //; symmetry. 
      move => h4 . case.  by transitivity (Void symbol) => //; symmetry. 
      move => h3 _. case.  by transitivity (Eps symbol) => //; symmetry. 
      move => h3. case. by transitivity (Void symbol) => //; symmetry.
    + move => h2. case. by transitivity (Void symbol) => //; symmetry.
- apply: cBar => c; case => [ss].
  case : (wder_Atom ss s) => [ -> | [ -> | ->]]. 
  * move => h1. apply cBar =>  [x]. case.  case => [tt]. 
    case : (wder_Atom tt s) => [ -> | [ -> | -> ]]. move => h2.
    + case. by transitivity (Atom s) => //; symmetry.
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3. case. by transitivity (Atom s) => //; symmetry. 
      move => h3 _. case. by transitivity (Eps symbol) => //; symmetry.
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4. case. by transitivity (Atom s) => //; symmetry.
      move => h4 _ . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 _ _ . case. by transitivity (Void symbol) => //; symmetry.
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3. case. by transitivity (Atom s) => //; symmetry.
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4. case. by transitivity (Atom s) => //; symmetry.
      move => h4 _ _ . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 _ . case. by transitivity (Void symbol) => //; symmetry.
      move => h3 _. case. by transitivity (Void symbol) => //; symmetry.
  * move => h1; apply cBar =>  [x]. case.  case => [tt]. 
    case : (wder_Atom tt s) => [ -> | [ -> | -> ]]. move => h2.
    + move =>  _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3 _. case. by transitivity (Atom s) => //; symmetry.
      move => h3. case. by transitivity (Eps symbol) => //; symmetry. 
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4 _. case. by transitivity (Atom s) => //; symmetry.
      move => h4 . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 _ _ . case. by transitivity (Void symbol) => //; symmetry.
    + move => h2. case. by transitivity (Eps symbol) => //; symmetry.
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4 _ _. case. by transitivity (Atom s) => //; symmetry.
      move => h4 . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 _ . case. by transitivity (Void symbol) => //; symmetry.
      move => h3. case. by transitivity (Eps symbol) => //; symmetry.
      move => h3 _. case. by transitivity (Void symbol) => //; symmetry.
  * move => h1; apply cBar =>  [x]. case.  case => [tt]. 
    case : (wder_Atom tt s) => [ -> | [ -> | -> ]]. move => h2.
    + move =>  _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3 _. case. by transitivity (Atom s) => //; symmetry.
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4 _. case. by transitivity (Atom s) => //; symmetry.
      move => h4 _ _ . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 . case. by transitivity (Void symbol) => //; symmetry.
      move => h3. case. by transitivity (Void symbol) => //; symmetry.
    + move => h2 _. apply cBar => [x']. case => [] [[uu]]. 
      case : (wder_Atom uu s) => [ -> | [ -> | -> ]].
      move => h3 _ _. apply cBar => [z]. case => [] [[[vv]]]. 
      case :(wder_Atom vv s) => [ -> | [ -> | -> ]].
      move => h4 _ _. case. by transitivity (Atom s) => //; symmetry.
      move => h4 _ . case. by transitivity (Eps symbol) => //; symmetry.
      move => h4 . case. by transitivity (Void symbol) => //; symmetry.
      move => h3 _. case. by transitivity (Eps symbol) => //; symmetry.
      move => h3. case. by transitivity (Void symbol) => //; symmetry.
    + move => h2. case. by transitivity (Void symbol) => //; symmetry.
(* Star *)
- by apply: finite_der_Star.
(* Plus *)
- by apply :finite_der_Plus.
(* And *)
- by apply :finite_der_And.
(* Conc *)
- by apply : finite_der_Conc.
(* Not *)
- by apply: finite_der_Not.
Defined.



End FiniteDer.
