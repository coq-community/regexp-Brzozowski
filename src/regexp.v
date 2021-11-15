(* begin hide *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype. 
From mathcomp Require Import bigop path.
Require Import glue.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits. 
(* end hide*)

Section RegExp. 
(** Base alphabet *)
Variable symbol : eqType.

Definition word := seq symbol. 

Canonical Structure word_eqType := [eqType of word]. 

Definition language := pred word. 

(* begin hide *)
Identity Coercion pred_of_language : language >-> pred. 

Implicit Type x y z : symbol. 

Implicit Type u v w : word. 

Implicit Type L : language. 

(* end hide *)
(** The Empty language *)
Definition void : language := pred0. 

(** The language that only recognize the empty word *)
Definition eps : language := pred1 [::]. 

(** The language that only recognize a particular letter *)
Definition atom x : language := pred1 [:: x]. 

(** The language that only recognize any letter *)
Definition dot :language := [pred x : word | size x == 1].

Lemma dotP : forall u, (u \in dot) = (size u == 1).
Proof.
by [].
Qed.

(** The complementary of language L *)
Definition compl L : language := predC L.

(** the language of words which are either in L1 or in L2 *)
Definition plus L1 L2 : language := [predU L1 & L2]. 

(** the language of words which are the concatenation of a word of L1 and
   a word of L2 *)
Definition conc L1 L2 : language := 
  fun v => [exists i : 'I_(size v).+1, L1 (take i v) && L2 (drop i v)].

(** the language of words which are in L1 _and_ in L2 *)
Definition prod L1 L2 : language := [predI L1 & L2].

Lemma prodP : forall {L1 L2 v},
   (v \in prod L1 L2) = (v \in L1) && (v \in L2 ).
Proof.
by move => L1 L2 v; rewrite inE.
Qed.

Lemma concP : forall {L1 L2 v}, 
  reflect (exists2 v1, v1 \in L1 & exists2 v2, v2 \in L2 & v = v1 ++ v2) 
          (v \in conc L1 L2). 
Proof. 
move=> L1 L2 v; apply: (iffP existsP) => [[i] | [v1 Lv1 [v2 Lv2 def_v]]]. 
  case/andP=> Lv1 Lv2; exists (take i v) => //; exists (drop i v) => //. 
  by rewrite cat_take_drop. 
have lt_v1_v: size v1 < (size v).+1 
   by rewrite def_v size_cat ltnS leq_addr. 
exists (Ordinal lt_v1_v); rewrite /= def_v. 
by rewrite take_size_cat // [L1 v1]Lv1 drop_size_cat. 
Qed.

(* Complementary is involutive *)
Lemma compl_invol : forall { L }, compl (compl L) =i  L.
Proof.
 by move => L v; rewrite inE /= /compl /= negbK.
Qed. 

Lemma complP : forall { L v}, (v \in compl L ) = ( v \notin L).
Proof. by []. Qed.

(** The residual of a language L with respect to x is the 
   set of words w such that xw is in L *)
Definition residual x L : language := [preim cons x of L]. 
 
Lemma residualE : forall x L u, (u \in residual x L) = (x :: u \in L). 
Proof. by []. Qed.

(** The Kleene star operator *)
Definition star L : language := 
  fix star v := if v is x :: v' then conc (residual x L) star v' else true. 

 
Lemma starP : forall {L v}, 
  reflect (exists2 vv, all [predD L & eps] vv & v = flatten vv)
          (v \in star L). 
Proof. 
move=> L v; 
  elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n. 
  by left; exists [::]. 
apply: (iffP concP) => [[u Lxu [v' starLv' def_v]] | [[|[|y u] vv] //=]]. 
  case/IHn: starLv' => [|vv Lvv def_v']. 
    by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl. 
  by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v']. 
case/andP=> Lyu Lvv [def_x def_v]; exists u; first by rewrite def_x.   
exists (flatten vv) => //; apply/IHn; last by exists vv.   
by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl. 
Qed.

(** Extended regular expression with boolean operators *)
Inductive regular_expression :=  
 | Void 
 | Eps
 | Dot  
 | Atom of symbol 
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
                                                            
(** Function that translate a regexp into its associated language *)
Fixpoint mem_reg e := 
  match e with 
  | Void => void      
  | Eps => eps 
  | Dot => dot
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
  | Not e1 => negb (has_eps e1)
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
apply/idP/orP.
- by move => h; left; rewrite inE h.
case => //.
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
    * by case/concP=> v; rewrite IHe1 => ? [w ? ->]; 
         exists (x :: v); last exists w.
    * move => hu. exists [::]. by rewrite -has_epsE. 
      exists (x::u) => //. by rewrite -residualE -IHe2.
    * by move=> _ [w e2w def_w]; right; rewrite IHe2 !inE def_w.
    move=> e1v [w e2w [def_x def_w]]; left; apply/concP.
    by exists v; [rewrite IHe1 def_x | exists w].
  apply/concP/concP => [[v] | ] /= ; rewrite -/mem_reg.
  + move => hv [w hw ->].  exists (x::v).
    * by rewrite -residualE -IHe1.
    by exists w.
  case => [[ | y v]]  hv [w hw] /=. 
  * by move: he; rewrite has_epsE hv.
  move/eqP. rewrite eqseq_cons. case/andP. 
  move/eqP => hx. move/eqP => hu. exists v. 
  * by rewrite IHe1 residualE hx.
  by exists w.
rewrite -topredE /=. rewrite /compl /=. rewrite topredE.
by rewrite IHe1.
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


Lemma star_id : forall l, star (star l) =i star l.
Proof.
move => l u. rewrite -!topredE /=. apply/starP/starP => [[vs h1 h2]  | ].
- elim: vs u h1 h2 => [ | hd tl Ih] u h1 h2.
* by exists [::] => //=.
* move: h1 => /=  h1. case/andP : h1. case/andP => hhd1 hhd2 htl.
  case: (Ih (flatten tl)) => //= [xs x1 x2]. case/starP: hhd2 => hds j1 j2.
  exists (hds++xs). rewrite all_cat. by apply/andP. rewrite h2 j2 /= x2.
  by rewrite flatten_cat.
- move => [hs h1 h2]. exists hs => //. apply/allP => x x1.
  move/allP: h1 => h1. case/andP: (h1 x x1) => /= h3 h4.
  rewrite h3 /=. apply/starP. exists [:: x] => /=. by rewrite h3 h4.
  by rewrite cats0.
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

Lemma wder_Dot : forall u, wder u Dot = Dot \/ wder u Dot = Eps \/ 
                           wder u Dot = Void.
Proof.
case => [ | hd ] /=. by left.
case => [ | hd' tl'] /=. by right; left.
by right; right ; apply wder_Void.
Qed.

Lemma wder_Atom : forall u n, wder u (Atom n) = Atom n \/  
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
Fixpoint wder_sigma (r1 r2: regular_expression) (s t:word) : 
  regular_expression :=
  match t with
  | nil => Conc (wder s r1) r2
  | hd :: tl => if has_eps (wder s r1) then 
      Plus (wder_sigma r1 r2 (s++hd::nil) tl) (wder t r2)
     else wder_sigma r1 r2 (s++hd::nil) tl
end.

Lemma wder_sigma_switch : forall t s x E F, 
  wder_sigma (der x E) F s t = wder_sigma E F [:: x & s] t.
Proof.
elim => [ | hd tl hi] s x E F //=. case (has_eps (wder s (der x E))).
congr Plus. by rewrite hi. by rewrite hi.
Qed.


Lemma wder_Conc: forall u E F, wder u (Conc E F) = wder_sigma E F  nil u.
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
   with s_i <> nil

  for example, (E* )/xy = E/xy.E* + \delta(E/x) E/y.E*
	       (E* )/xyz = E/xyz.E* + \delta(E/x) E/yz.E* +
	      	          \delta(E/x)\delta(E/y) E/z.E*  +
			  \delta(E/xy) E/z.E*
 
  to keep it simple, I just say that
  (E* )/[] = E* and (E* )/x::s = (E.E* )/s as we already know
  the form of (P.Q)/s
*) 



End RegExp.


 
