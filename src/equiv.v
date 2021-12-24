(* begin hide *)
From Coq Require Import RelationClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
From RegLang Require Import languages.
From RegexpBrzozowski Require Import glue gfinset regexp finite_der.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits. 

(* end hide *)

(** From now on, we consider the alphabet to be {0, 1}, but the
    following also holds for any _finite_ set with a decidable 
    equality *)
Section Equiv.

Definition bregexp := regular_expression [eqType of bool].
Definition bword := word [eqType of bool].


(** The similarity is still abstracted *)
Variable similar : bregexp -> bregexp -> bool.

Definition sim : grel bregexp := similar.
Definition nsim r1 r2 := ~ sim r1 r2.

Context `{Equivalence bregexp similar}.
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

Let has_eps_sim := has_eps_sim similar_ok.

(** Two regexp are equivalent if their associated languages are equal *)
Definition EQUIV (E F:bregexp) := forall s:bword, (s \in E ) = (s \in F).
Notation "E ≡ F" := (EQUIV E F) ( at level 30).


(** This can be translated in the following form *)
Lemma EQUIV2 : forall E F, E ≡ F <-> 
  forall s, (has_eps (wder s E)) = (has_eps (wder s F)).
Proof.
rewrite /EQUIV => E F. split => h.
- move => s. rewrite -2!mem_wder 2!mem_derE. by apply: h.
- move => s. rewrite -2!mem_derE 2!mem_wder. by apply: h.
Qed.

Definition set_pair_der (E F:bregexp) : gset (bregexp*bregexp) := 
  fun G => let (e,f) := G in 
     exists2 s, similar e (wder s E) & similar f (wder s F).

Definition set_pair_ders (E F:bregexp) : gset (bregexp*bregexp) := 
  fun G => let (e,f) := G in 
 exists2 s, e = (wder s E) & f = (wder s F).

(** Or even further simplified:
   E and F are equivalent iff
   forall u:word, delta (E/u) = delta (F/u)
*)
Lemma EQUIV3 : forall E F, E ≡ F <-> 
  (forall e f, set_pair_der E F (e,f) -> has_eps e = has_eps f).
Proof.
rewrite /EQUIV => E F; split => h.
- rewrite /set_pair_der. move => e f [s] h1 h2.
  rewrite (has_eps_sim h1) (has_eps_sim h2) -!mem_wder !mem_derE. 
  by apply: h.
- rewrite /set_pair_der in h => s. apply EQUIV2. move => t.
  rewrite (h (wder t E) (wder t F)) => //.
  exists t; reflexivity.
Qed.

(* begin hide *)
Definition wsim (a b: bword) : Prop := True.
Definition nwsim (a b: bword) : Prop := False.

Lemma wsim_dec : forall (a b : bword), {wsim a b}+{~wsim a b}.
Proof.
rewrite /wsim => a b. by left.
Defined.

Global Instance wsim_Eq : Equivalence wsim.
Proof. 
split; by move => s.
Qed.

Definition sim3 := eq_prod (eq_prod sim sim) wsim.

Global Program Instance sim3_Eq : Equivalence sim3.

Lemma sim_dec3 : forall x y, {sim3 x y}+{~sim3 x y}.
Proof.
case => [[a1 b1] s1] [[a2 b2] s2]. rewrite /sim3 /wsim /sim /=.
case: (similar a1 a2). case: (similar b1 b2). 
by left; split.
by right; case => [[]].
by right; case => [[]].
Defined.

Definition bT : bword -> Prop := fun _ => True.

Definition sim_dec2 := eq_prod_dec (sim_dec similar) (sim_dec similar).

Definition sim2 := eq_prod similar similar.
Definition nsim2 := r_prod nsim nsim.
(* end hide *)

(** The derivation function that takes a list and return the same list +
    the derivatives of each element, if it was not already there.
    To be able to give a witness in case of non-equivalence, we store the
    word use for derivation (actually we store the reverse word for
    efficienty *)
Definition der1 (E:bregexp) : bregexp  := der true E.
Definition der0 E := der false E.

(* words are stored in reverse *)
Fixpoint DER l := match l with
 | [::] => [::]
 | ((hdl,hdr),s) :: tl =>
   [:: (der1 hdl, der1 hdr, true::s) , (der0 hdl, der0 hdr, false::s) &
    DER tl ]
end.


Fixpoint DER1 l := match l with
 | [::] => [::]
 | (hd,s) :: tl => [:: (der1 hd,true::s) , (der0 hd,false::s) & DER1 tl ]
end.

Definition set_of_der := set_of_der similar.

(** The set { (e,f) | exists u, e ~ E/u & f ~ F/u } is finite
    because it is included in Der E x Der F *)
Lemma set_pair_der_is_finite: forall E F, 
  Bar (r_prod (r_prod nsim nsim) nwsim) (Prod (set_pair_der E F) bT).
Proof.
move => E F. 
apply (@Bar_gset_incl _   (Prod (Prod (set_of_der E) (set_of_der F)) bT)).
apply Bar_gset_prod. apply Bar_gset_prod. 
by apply finite_number_of_der. 
by apply finite_number_of_der.
apply cBar => x _. apply cBar => y. case => _. by rewrite /nwsim.
case => [[e f] s]. rewrite /set_pair_der /= => [[[u sime simf] _]].
split => //. split. by exists u. by exists u.
Qed.

Lemma Set_of_der_compat: forall E F, 
 E_compat sim3 (Prod (set_pair_der E F) bT).
Proof.
rewrite /E_compat /set_pair_der => E F [[e f] s] [[e' f'] s'] [[] ]. 
rewrite /sim => h1 h2 _ [[u h3 h4] _].
split => //. exists u.
- transitivity e => //; by symmetry. 
transitivity f => //; by symmetry. 
Qed.

Lemma Set_of_der_compat1 : forall E, E_compat sim (set_of_der E).
Proof.
rewrite /E_compat. by apply : set_of_der_compat.
Qed.

(**  L(x) = L(y) -->  L(der a x) = L(der a y) *)
Lemma in_der_compat : forall (r1 r2:bregexp) , r1 ≡ r2 ->
  forall a,(der a r1) ≡ (der a r2). 
Proof.
move => r1 r2 heq a u.
by rewrite !derE !in_residual !heq.
Qed.

Lemma in_wder_compat : forall (r1 r2:bregexp), r1 ≡ r2 -> forall s,
  (wder s r1) ≡ (wder s r2).
Proof.
move => r1 r2 heq. elim/last_ind => [ | s a hi] //= u.
rewrite -!cats1 !wder_cat /=. by apply in_der_compat.
Qed.

(** set of derivative without _up to equality_ and not symmetry *)
Definition ders (E:bregexp) := fun G => exists s, G = wder s E.

(** inclusion for = implies inclusion for ~ *)
(* TODO: maybe move this to finite_der_bis.v since I 
also use it there 
*)
Lemma lincl_mem_sim : forall (A:eqType) (eqA: grel A) 
  (hE: Equivalence eqA) (hdec: forall x y, {eqA x y}+{~eqA x y}),
  forall (l:seq A) a, (a \in l) -> InA hdec l a.
Proof.
move => A eqA hE hdec. elim => [ | hd tl hi] //= a.
rewrite in_cons; case/orP => hu.
- rewrite (eqP hu). case: (hdec hd hd) => //=. case; by reflexivity.
- case: (hdec a hd) => //= _. by apply: hi.
Qed.

(** subset for = implies subset for ~ *)
Lemma lincl_sim : forall (A:eqType) (eqA: grel A) (hE: Equivalence eqA) 
 (hdec: forall x y, {eqA x y}+{~eqA x y}),
 forall (l l':seq A), lincl l l' -> r_subset eqA l l'.
Proof.
move => A eqA hE hdec l l' hl. apply/(@R_elim _ _ hE hdec).
elim : l l' hl => [ | hd tl hi] l' //=. case/andP => hhd htl x.
case: (hdec x hd) => //=. move => heq _. rewrite (InA_eq hdec l' heq). 
by apply: lincl_mem_sim. 
move => _ hin. by apply: hi.
Qed.


Global Program Instance sim2_Eq : Equivalence (eq_prod sim sim).

Lemma In_DER1 : forall f f' v Y, (f,f',v) \in Y -> 
  InA sim_dec3 (DER Y) (der true f, der true f',true::v).
Proof.
move => f f' v; elim => [ | [[hdl hdr] s] tl hi] //.
rewrite in_cons. case/orP.
- by move => heq; rewrite -(eqP heq) {1}/DER -/DER InA_hd. 
- move => hIn. 
  rewrite {1}/DER -/DER InA_tl //. 
  rewrite {1}/DER -/DER InA_tl //.
  by apply: hi.
Qed.

Lemma In_DER0 : forall f f' v Y, (f,f',v) \in Y ->
   InA sim_dec3 (DER Y) (der false f, der false f',false::v).
Proof.
move => f f' v; elim => [ | [[hdl hdr] s] tl hi] //.
rewrite in_cons. case/orP.
- by move => heq; rewrite -(eqP heq) {1}/DER -/DER InA_tl // InA_hd. 
- move => hIn. 
  rewrite {1}/DER -/DER InA_tl //. 
  rewrite {1}/DER -/DER InA_tl //.
  by apply: hi.
Qed.

Lemma tool_bl : forall (Y:seq (bregexp*bregexp*bword)), 
  r_subset sim3 (DER Y) Y ->
  forall e e', ((e,e',[::]) \in Y) -> 
  forall u, exists f, exists f', exists v, [/\ (f,f',v) \in Y , 
    (wder u e) ≡ f & (wder u e') ≡ f'].
Proof.
move => Y hsub e e' he.
elim/last_ind => [ | u a hi] /=.
- by exists e; exists e'; exists [::]; split .
- case: hi => f [f' [v [hf1 hf2 hf3]]].
  move/(@R_elim _ _ sim3_Eq sim_dec3) : hsub.
  have hf : (InA sim_dec3 (DER Y) (der a f,der a f',a::v)). 
  + case: a. 
    by apply: In_DER1.
    by apply: In_DER0.
  rewrite -!cats1 !wder_cat  => hsub.
  have hg : (InA sim_dec3 Y (der a f,der a f',a::v)).
  + by apply: hsub. 
  case: (InA_inv sim3_Eq hg) => [[[g g'] w]] hg1. 
  rewrite /sim3 /sim => [[[ hg2l hg2r] _]].
  exists g; exists g'; exists w; split => //.
  + move => s /=. 
    rewrite (in_der_compat hf2 a s).
    by apply similar_ok; symmetry.  
  + move => s /=. 
    rewrite (in_der_compat hf3 a s).
    by apply similar_ok; symmetry.  
Qed.

(** function that tests if a list of pairs validate the delta operator *)
Definition delta2 (efw:bregexp * bregexp * bword) := let (ef,_) := efw in
 let (e,f) := ef in has_eps e == has_eps f.


(** a derivative for = is a derivative for ~ *)
Lemma ders2der : forall E F,
 (forall x, Prod (set_pair_ders E F) bT x -> 
           Prod (set_pair_der E F) bT x).
Proof.
rewrite /set_pair_ders /set_pair_der => E F [[e f] u] [[s -> ->] _].
split => //. by exists s; reflexivity.
Qed.

(** the derivative of an = derivative is an = derivative *)
Lemma gpred_list_DERs : forall E F,
(forall X, gpred_list (Prod (set_pair_ders E F) bT) X -> 
           gpred_list (Prod (set_pair_ders E F) bT) (DER X)).
Proof.
move => E F.
elim => [ | [[hdl hdr] u] tl] //=  => hi.
case => [[[s -> ->] _]] htl; split.
by split => //; exists (s++[::true]); rewrite /der1 !wder_cat /=. split.
by split => //; exists (s++[::false]); rewrite /der0 !wder_cat /=.
by apply: hi.
Qed. 

(** sets of pair of derivative is inductively finite for ~ *)
Lemma set_pair_der_finite: forall E F, Bar (neq sim3) (Prod (set_pair_der E F) bT).
Proof.
move => E F.
apply: (@Bar_grel_incl _ _  (r_prod nsim2 nwsim)).
- by apply set_pair_der_is_finite.
rewrite /nsim2 /nsim /r_prod /neq /sim3 /eq_prod /sim  =>
   [[[a a'] u]] [[b b'] u'].
case: (similar a b) => /=. move => hneq. left; right => hneq2.
by apply: hneq. move => _. by left; left.
Qed.  

Lemma gpred_listP2 : forall (A:eqType) (E:gset A) (l:seq A) (x:A), 
  (x \in l) -> gpred_list E l -> E x.
Proof.
move => A E l x. elim: l => [ | hd tl hi] //=.
rewrite in_cons. case/orP => hu [hhd htl]. by rewrite (eqP hu).
by apply: hi.
Qed.


Lemma DER_cat : forall l1 l2, 
  sim_incl sim_dec3 (DER (l1 ++ l2)) ((DER l1) ++ (DER l2)).
Proof.
move => l1 l2; elim : l1 => [ | hd tl ] //=.
- by apply : sim_incl_refl. 
- case: hd => [[hdl hdr] s] hi.
  rewrite !cat_cons. 
  change [:: (der1 hdl, der1 hdr,true::s ), 
             (der0 hdl, der0 hdr,false::s) & DER (tl ++l2)]
    with ([:: (der1 hdl, der1 hdr,true::s); 
              (der0 hdl, der0 hdr,false::s)]++(DER (tl ++l2))).
  change [:: (der1 hdl, der1 hdr,true::s),
             (der0 hdl, der0 hdr,false::s) & DER tl ++ DER l2]
    with ([:: (der1 hdl, der1 hdr,true::s); 
              (der0 hdl, der0 hdr,false::s)]++(DER tl ++ DER l2)).
  by rewrite sim_incl_lcongr.
Qed.

Scheme Acc_rect_dep := Induction for Acc Sort Type.

(* begin hide *)
Definition build_list_fun_acc : forall (E F:bregexp), 
 forall (X Y:seq (bregexp* bregexp*bword)),
 Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X ->
 gpred_list (Prod (set_pair_ders E F) bT) X ->
 gpred_list (Prod (set_pair_ders E F) bT) Y ->
 ldisjoint sim_dec3 X Y ->
 seq (bregexp*bregexp*bword).
Proof.
move => E F X Y ha. move: Y.
elim ha using Acc_rect_dep. clear X ha.
move => X hp hi [ | hdY tlY] hpred1 hpred2.
- move => _; exact X.
- move/ldisjointP => hd.
  set Z := (X ++ hdY :: tlY).
  apply: (hi Z _ _ (lminus sim_dec3 (DER (hdY :: tlY)) Z)).
  + apply (gpred_list_incl (@ders2der E F)). by apply gpred_list_cat.
  + apply/(@sub_elim _ _ _ sim_dec3). 
    split; first by move => x hx; rewrite InA_cat hx.
    exists hdY. move : (hd hdY). case: (InA sim_dec3 X hdY) => //=.
    case : sim_dec3 => //=. move => _. by case. 
    case; by reflexivity. rewrite InA_cat /=.
    case: sim_dec3 => //=. by rewrite orbT.
    by case; reflexivity.
  + by apply gpred_list_cat.
  + apply: lminus_pred. by apply : gpred_list_DERs.
  + by apply: ldisjoint_lminus.
Defined.

Lemma lAcc: forall (E F:bregexp) (X:seq (bregexp*bregexp*bword)), 
  Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X.
Proof.
move => E F X.
apply (guard 100). move => X'. apply: wf_sup.
- by apply: sim_dec3.
- by apply: Set_of_der_compat.
- by apply: set_pair_der_finite.
Defined.

(* simple proof of (e,f) \in [ (e,f) ] *)
Lemma EF_in_der : forall (E F:bregexp), gpred_list (Prod (set_pair_ders E F) bT) [:: (E,F,[::])].
Proof.
rewrite /set_pair_ders /= => E F. split => //. by split; [exists [::] | ].
Qed.
(* end hide *)

(** Major function: this function build the set of pairs of derivatives from two regular expressions, and then extract a list of pairs (with witness)
    from it (since it is inductively finite set) *)
Definition build_list_fun : bregexp -> bregexp -> 
 seq (bregexp*bregexp*bword).
move => E F.
apply (@build_list_fun_acc E F [::(E,F,[::])] 
                       (lminus sim_dec3 (DER [::(E,F,[::])]) [::(E,F,[::])])
                       (lAcc E F [:: (E,F,[::])]) (EF_in_der E F)).
- apply: lminus_pred. apply: gpred_list_DERs. by apply: EF_in_der.
- by apply: ldisjoint_lminus.
Defined.


(** Properties of this list *)
(** 1: (e,f) is in the list(e,f) *)
Lemma l1 : forall (E F:bregexp), 
 forall (X Y:seq (bregexp* bregexp*bword))
 (ha: Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X)
 (hp1: gpred_list (Prod (set_pair_ders E F) bT) X)
 (hp2: gpred_list (Prod (set_pair_ders E F) bT) Y)
 (hd : ldisjoint sim_dec3 X Y),
 lincl X (build_list_fun_acc ha hp1 hp2 hd).
Proof.
move => E F X Y ha. move: Y.
elim ha using Acc_rect_dep. clear X ha.
move => X hp hi [ | hdY tlY] hp1 hp2 /=. 
- move =>  _; by apply : lincl_refl.
- move =>  hd. apply: (@lincl_trans _ (X ++ hdY :: tlY)).
  by apply: lincl_catr; apply: lincl_refl.
  by apply: hi.
Qed.


(** 2: the list is made of = derivatives *)
Lemma l2 : forall (E F:bregexp),
 forall (X Y:seq (bregexp* bregexp*bword))
 (ha: Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X)
 (hp1: gpred_list (Prod (set_pair_ders E F) bT) X)
 (hp2: gpred_list (Prod (set_pair_ders E F) bT) Y)
 (hd : ldisjoint sim_dec3 X Y),
 (gpred_list (Prod (set_pair_ders E F) bT)) 
            (build_list_fun_acc ha hp1 hp2 hd).
Proof.
move => E F X Y ha. move : Y.
elim ha using Acc_rect_dep. clear X ha.
move => X hp hi [ | hdY tlY] hp1 hp2 /=. 
- move => _. by apply: hp1.
- move => hd. by apply: hi. 
Qed.

(** 3: the list is stable by derivation *)
Lemma l3 : forall (E F:bregexp),
 forall (X Y:seq (bregexp* bregexp*bword))
 (ha: Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X)
 (hp1: gpred_list (Prod (set_pair_ders E F) bT) X)
 (hp2: gpred_list (Prod (set_pair_ders E F) bT) Y)
 (hd : ldisjoint sim_dec3 X Y)
 (hs: sim_incl sim_dec3 (DER X) (X ++ Y)),
  r_subset sim3 (DER (build_list_fun_acc ha hp1 hp2 hd))
                (build_list_fun_acc ha hp1 hp2 hd).
Proof.
move => E F X Y ha. move: Y.
elim ha using Acc_rect_dep. clear X ha.
move => X hp hi [ | hdY tlY] hp1 hp2 /=. 
- rewrite cats0 => _ hs. by  apply/(@sim_inclP _ _ _ sim_dec3). 
- move => hd hs. apply: hi.
  apply: (@sim_incl_trans _ _ _ _ (DER X ++ DER (hdY :: tlY)))
   => /=.
  by apply: DER_cat. 
  rewrite sim_incl_cat. apply/andP; split. 
  by apply: sim_incl_cat2l. 
  by rewrite lminus_incl.
Qed.

(** Function which test the equivalence of regular expression *)
Definition bregexp_eq (r1 r2: bregexp) : bool :=
  (all delta2  (build_list_fun r1 r2)). 

(** Proof of correctness of the boolean function *)
Lemma bregexp_eqP : forall (r1 r2:bregexp),
  reflect (r1 ≡ r2) (bregexp_eq r1 r2).
Proof.
move => r1 r2.
have h1 : (r1,r2,[::]) \in build_list_fun r1 r2.  
- rewrite /build_list_fun.
  apply: (@lincl_mem _ [:: (r1,r2,[::])]). 
  by apply: l1. by rewrite /= in_cons eq_refl. 
have h2 : r_subset sim3 (DER (build_list_fun r1 r2)) 
                        (build_list_fun r1 r2).
- rewrite /build_list_fun; apply: l3.
  by rewrite lminus_incl.
apply: (iffP allP).
- rewrite /bregexp_eq => h. apply EQUIV3.
  move => e f. rewrite /set_pair_der  => [[s he hf]].
  rewrite (has_eps_sim he) (has_eps_sim hf) !has_epsE.
  case: (tool_bl  h2 h1 s) => e' [f' [v' [h'1 h'2 h'3]]].
  rewrite (h'2 [::]) (h'3 [::]) -!has_epsE. move: (h (e',f',v') h'1).
  rewrite /delta2 => heq. by rewrite (eqP heq).
- move => h [[e f] v] hIn. rewrite /delta2 !has_epsE.
  have: (Prod (set_pair_ders r1 r2) bT (e,f,v)).
  + apply: (gpred_listP2 hIn). by apply: l2.
  case => [[s -> ->]] _. apply/eqP. by apply in_wder_compat.
Qed.

Lemma bregexp_dec : forall (r1 r2:bregexp), {r1 ≡ r2}+{~ r1 ≡ r2}.
Proof.
move => r1 r2.
have:= bregexp_eqP r1 r2.
case : (bregexp_eq r1 r2). move => h. left. by apply/h.
move => h. right. by move/h.
Qed.

(** For free: Inclusion for languages *)
Definition SUB (r1 r2: bregexp) := forall s, (s \in r1) -> (s \in r2).

Lemma SUB2 : forall r1 r2, SUB r1 r2 <->  r2 ≡ (Plus r1 r2).
Proof.
rewrite /SUB /EQUIV => r1 r2; split => h s.
- rewrite -!topredE /=. apply/idP/orP.
  move => h'; by right. case => hu //. by apply: h.
- rewrite (h s) -!topredE /= => h1. apply/orP. by left.
Qed. 

(** To test the inclusion of L(r1) in L(r2), it suffices to test
    that r1 + r2 and r2 are equivalent *)
Definition bregexp_sub (r1 r2:bregexp) := bregexp_eq r2 (Plus r1 r2).

(* correctness of bregexp_sub *)
Lemma bregexp_subP : forall r1 r2, 
  reflect (SUB r1 r2) (bregexp_sub r1 r2).
Proof.
rewrite /SUB /bregexp_sub => r1 r2. apply: (iffP idP).
- move/bregexp_eqP => h. by apply SUB2.
- move => h. apply/bregexp_eqP. by apply SUB2.
Qed.

(** In case of non equivalence, here is the function that extracts a 
    witness *)
Fixpoint extract_word (l: seq (bregexp*bregexp*bword)) : option bword :=
 match l with
  | [::] => None
  | ((a,b),u) :: tl => if has_eps a == has_eps b 
                       then extract_word tl
                       else Some u
end.

Definition bregexp_ce (r1 r2:bregexp) : option bword :=
  extract_word (build_list_fun r1 r2).

Lemma extract_word_tool : forall l, 
 match extract_word l with
  | None => all delta2 l
  | Some u => exists e,exists f, (e,f,u) \in l /\ (predC delta2) (e,f,u)
end.
Proof.
elim => [ | [[a b] u] tl hi] //=.
case heq : (has_eps a == has_eps b) => //=.
- move : hi. case: (extract_word tl) => //=. move => w [e [f [h1 h2]]].
  exists e; exists f; rewrite in_cons. by rewrite h1 orbT.
- by exists a; exists b; rewrite in_cons heq eq_refl.
Qed.

(* begin hide *)
Definition ff (r1 r2:bregexp) (efw:bregexp*bregexp*bword) :=
 let (ef,w) := efw in let (e,f) := ef in 
  (wder (rev w) r1) ≡ e /\
  (wder (rev w) r2) ≡ f.

Lemma wder_rcons : forall  a u (r:bregexp), 
  wder (rcons u a) r = der a (wder u r).
Proof.
move => a. elim => [ | hd tl hi] //= r.
Qed.


(* test about the added words *)
Lemma DER_preserves_lang : forall E F X, 
  gpred_list (ff E F) X -> gpred_list (ff E F) (DER X).
Proof.
move => E F. elim => [ | [[r1 r2] u] tl hi] //= [[h1 h2] h3]. 
rewrite !rev_cons !wder_rcons /=. split.
- split. move => s. by apply in_der_compat.
- move => s;  by apply in_der_compat.
- split. split. move => s;  by apply in_der_compat.
- move => s;  by apply in_der_compat.
by apply: hi.
Qed.

Lemma l4 : forall (E F:bregexp),
 forall (X Y:seq (bregexp*bregexp*bword))
 (ha : Acc (gpred_list (Prod (set_pair_der E F) bT)) (sup sim3) X)
 (hp1 : gpred_list (Prod (set_pair_ders E F) bT) X) 
 (hp2 : gpred_list (Prod (set_pair_ders E F) bT) Y)
 (hs: ldisjoint sim_dec3 X Y), 
 gpred_list (ff E F) X -> 
 gpred_list (ff E F) Y -> 
 gpred_list (ff E F) (build_list_fun_acc ha hp1 hp2 hs).
Proof.
move => E F X Y ha. move: Y.
elim ha using Acc_rect_dep. clear X ha.
move => X hp hi [ | hdY tlY] hhp1 hp2 hs /=. 
- by move => h _.
- move => hX hY. apply: hi. apply/gpred_list_cat; split => //.
  apply: lminus_pred.
  clear hp2 hs. case: hdY hY => [[hdl hdr] s] [].
  rewrite {1}/ff  => [[h1 h2]] h3 /=; split.
  + rewrite !rev_cons !wder_rcons. split.
    move => w. by apply in_der_compat.
    move => w. by apply in_der_compat.
    split.
  + rewrite !rev_cons !wder_rcons. split.
    move => w. by apply in_der_compat.
    move => w. by apply in_der_compat.
  + by apply: DER_preserves_lang.
Qed.
(* end hide *)
(** Correctness of the above function:
    - if r1 and r2 are equivlent, we return a proof of it
    - if not, we return a word u and a proof that
      either u in L(r1) and not u in L(r2) or the other
      way around
*)
Lemma bregexp_ceP : forall r1 r2, match bregexp_ce r1 r2 with
 | None => r1 ≡ r2
 | Some s => ((rev s \in r1) && (rev s \notin r2)) \/
             ((rev s\notin r1) && (rev s\in r2))
end.
Proof.
move => r1 r2.
have htemp : gpred_list (ff r1 r2) [:: (r1, r2, [::])].
- rewrite /ff /=. by split. 
have htemp2: gpred_list (ff r1 r2) 
  (lminus sim_dec3 (DER [::(r1,r2,[::])]) [::(r1,r2,[::])]).
- apply: lminus_pred. by apply: DER_preserves_lang.
rewrite /bregexp_ce. 
move: (extract_word_tool (build_list_fun r1 r2)). 
case: extract_word. 
- move => a [e [f [h1]]]. rewrite /predC /= => h2.
  have hpred : gpred_list (ff r1 r2) (build_list_fun r1 r2). 
  + by rewrite /build_list_fun; apply: l4.
  move: (gpred_listP2 h1 hpred). rewrite /ff => [[hl1 hl2]].
  move : (hl1 [::]) (hl2 [::]); clear hl1 hl2.  
  rewrite -!mem_derE !mem_wder /= => -> ->. move : h2.
  case: (has_eps e) => //=.  case: (has_eps f) => //= _; by left.
  case: (has_eps f) => //= _; by right.
- by move/bregexp_eqP. 
Qed.

(** Extract the list of derivatives for a regexp *)
Definition build_list_der (E:bregexp) : seq (bregexp*bword) :=
 strip ( build_list_fun E E).  

Lemma build_list_der_ok : forall (E:bregexp) u, exists F:bregexp, exists v, 
  ((F,v) \in (build_list_der E)) /\ (wder u E) ≡ F. 
Proof.
move => E u.
set L := build_list_fun E E. 
case: (@tool_bl L _ E E _ u) => [ | | f [f' [v [h1 h2 h3]]]].
- rewrite /L /build_list_fun. apply: l3. 
  by apply: lminus_incl.
-  apply: (@lincl_mem _ [:: (E,E,[::])]).
   by apply: l1. by rewrite /= in_cons eq_refl.
exists f; exists v; split => //.
rewrite /build_list_der. move/strip_in : h1.
rewrite /L => h; exact h.
Qed.

End Equiv.
