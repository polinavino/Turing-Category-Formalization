Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Category".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Essentials".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Functor".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Cat".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\NatTrans".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Limits".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Archetypal".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Coq_Cats\Type_Cat".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Ext_Cons".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Ext_Cons\Prod_Cat".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Basic_Cons".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Coq_Cats".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Basic_Cons".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Abst_Comp".
Add LoadPath "C:\Users\Polina\Documents\Coq\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Functor".

Require Import Main_Func.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Main_Category.
Require Import CCC.
Require Import Restriction.
Require Import Set_Cat.

Generalizable All Variables.

(*AXIOM proof irrelevance*)
Axiom pf_ir : forall A: Prop , forall p q:A, p=q.


(* objects and morphisms in the category Par *)
Definition hom := fun (A B : Set) => {P:A -> Prop & ( forall x:A, P x -> B )}.

Definition obj := Set.

(* Equality in Par *)
Lemma HomParEqv: forall  a b: obj,   (hom a b) -> (hom a b) -> Prop  .
Proof.
  unfold hom. intros.
  destruct X; destruct X0.
  exact ((forall (z:a), (x z <-> x0 z)) /\ ( forall z:a,forall pf:x z,forall pf1:x0 z, x z -> (b0 z pf = b1 z pf1))). 
Defined.


(* AXIOM equality in Par *)
Axiom par_eqv_def : forall a b: obj, forall f g : hom a b, HomParEqv a b f g -> f = g.
 

(* composition in Par *)
Definition Compose : forall A B C : Set, hom A B -> hom B C -> hom A C.
Proof.
  unfold hom.
  intros.
  destruct X.
  destruct X0.
  exists (fun (z:A) => (x z /\ (forall (p:x z), (x0 (b z p))))).
  intros.
  destruct H.
  exact (c (b x1 H) (H0 H) ).
Defined.

(* identity in Par *)
Definition Id : forall A : Set, hom A A.
Proof.
  unfold hom.
  intros.
  exists (fun (a:A) => True).
  intros.
  auto.
Defined.

Instance Par_Cat : Category :=
{
  Obj := obj;

  Hom := hom;

  compose := Compose;

  id := Id
}.
Proof.
(* associativity *)
  unfold hom. intros.
  apply (par_eqv_def a d (Compose a b d f (Compose b c d g h)) (Compose a c d (Compose a b c f g) h)).
  destruct f; destruct g; destruct h.
  compute. split. intros. split; split.
  split. destruct H. auto.
  intros. destruct H.
  elim (H0 p). intros; auto.

  intros. 
  destruct p; destruct H. destruct (H0 x2).
  exact (H2 (x3 x2)).
   
  destruct H; destruct H; auto.
  split; destruct H. destruct H. exact (H1 p).

  intro. generalize (H0 H). compute. destruct H.
  rewrite (pf_ir  (x z)  x2 p).
  rewrite (pf_ir (x0 (b0 z p)) (x3 p) p0).
  auto.

  intros. destruct pf. destruct a0.  destruct H. destruct (H0 H). destruct pf1. destruct a1.
  rewrite <- (pf_ir (x z) x2 x6).
  rewrite <- (pf_ir (x0 (b0 z x2)) (x7 x2) x3).
  rewrite (pf_ir  (x1 (c0 (b0 z x2) (x7 x2))) (x4 (x7 x2)) (x5 (conj x2 x7))).
  auto.


(* symmetric associativity *)
  unfold hom. intros.
  apply (par_eqv_def a d (Compose a c d (Compose a b c f g) h)  (Compose a b d f (Compose b c d g h))).
  destruct f; destruct g; destruct h.
  compute. split. intros. split; split.
  destruct H. destruct H. auto.
  split. destruct H. destruct H.
  exact (H1 p).
 
  intro. destruct H. generalize (H0 H). intro. destruct H.
  rewrite <- (pf_ir (x z) p x2) in H1.
  rewrite <- (pf_ir (x0 (b0 z p)) (x3 p) p0).
  auto.

  split; destruct H.
  auto.
  intro.
  destruct (H0 p). auto.
  intro. destruct p.
  destruct H. destruct (H0 x2). exact (H2 (x3 x2)).

  intros. destruct pf; destruct pf1.
  destruct a0.  destruct (a1 x3).
  rewrite <- (pf_ir (x z) x3 x4).
  rewrite <- (pf_ir (x0 (b0 z x3)) (x5 x3) x6).
  rewrite (pf_ir (x1 (c0 (b0 z x3) (x5 x3))) (x2 (conj x3 x5)) (x7 (x5 x3))).
  auto.

(* id left unit *)
  intros.
  apply (par_eqv_def a b (Compose a b b h (Id b)) h ).
  destruct h. compute.
  split. intros. split. intro.
  destruct H; auto.
  intro; split. auto. intro; auto.

  intros; destruct pf.
  rewrite (pf_ir (x z) x0 pf1). auto.

(* id right unit *)
  intros.
  apply (par_eqv_def a b (Compose a a b (Id a) h) h ).
  destruct h. compute.
  split. intros. split. intro.
  destruct H; auto.
  intro; split. auto. intro; auto.

  intros; destruct pf.
  rewrite (pf_ir (x z) (x0 t) pf1). auto.
Defined.


(* define restriction combinator map that makes Par a restriction category *)
Definition rc_ParMap : forall a b : Par_Cat, Hom a b -> Hom a a.
Proof.
  intros a b. compute. intro. destruct X.
  exists x. intros. exact x0.
Defined.

Print rc_ParMap.


(* Instantiate the restriction combinator for Par *)
Definition rc_Par :  RestrictionComb Par_Cat.
Proof.
  exists rc_ParMap; intros.

(* rc1 *)
  apply (par_eqv_def a b (f ∘ rc_ParMap a b f) f).
  destruct f. compute. split. intros. split.
  intros. destruct H; auto.
  split; intros; auto.
  intros. destruct pf.
  rewrite (pf_ir (x z) (x1 x0) pf1).
  auto.
  
(* rc2 *)
  apply (par_eqv_def a a (rc_ParMap a c g ∘ rc_ParMap a b f) (rc_ParMap a b f ∘ rc_ParMap a c g)).
  destruct f. destruct g. compute. split. intros. split.
  intros. destruct H; auto.
  split; intros; auto.
  destruct H. exact (H0 H). 
  destruct H; auto.

  intros. destruct pf. destruct pf1. auto.

(* rc3 *)
  apply (par_eqv_def a a (rc_ParMap a c (g ∘ rc_ParMap a b f)) (rc_ParMap a c g ∘ rc_ParMap a b f)).
  destruct f. destruct g. compute. split. intros. split.
  intros. destruct H; auto.
  split; intros; auto.
  destruct H. auto. destruct H. exact (H0 H). 

  intros. destruct pf. destruct pf1. auto.

(* rc4 *)
  apply (par_eqv_def a b (rc_ParMap b c g ∘ f) (f ∘ rc_ParMap a c (g ∘ f))).
  destruct f. destruct g. compute. split. intros. split.
  intros. destruct H. auto.
  split. destruct H. destruct H. auto.
  destruct H. intros. destruct H. exact (H1 p). 

  intros. destruct pf. destruct pf1. 
  rewrite (pf_ir (x z) x1 (x3 a0)).
  auto.
Defined.

(* define Par as an instance of a restruction category *)
Instance Par_isRC : RestrictionCat Par_Cat rc_Par := {   }.


(* Below we will show that Tot(Par) is isomorphic to Set 
    This is not yet completed, and so does not compile *)

Instance Par_isCRC : CartesianRestr

Instance TotPar_Set_Cat_Eqv : Functor Set_Cat (Tot rc_Par Par_isRC).
Proof.
  destruct Set_Cat. destruct (Tot rc_Par Par_isRC). 
  assert (F0 : Set_Cat -> (Tot rc_Par Par_isRC)).
  simpl. intro. exists X. auto.
  assert (F1 : ∀ a b : Set_Cat, Hom a b → Hom0 (F0 a) (F0 b)).
exists. destruct Functor. compute.

Class Functor (C C' : Category) : Type := 
{
  (* Object map *)
  FO : C → C';

  (* Arrow map *)
  FA : ∀ {a b}, Hom C a b → Hom C' (FO a) (FO b);
  intro. unfold Functor.


