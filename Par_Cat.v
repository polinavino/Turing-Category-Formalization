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
Require Import Range.
Require Import Set_Cat.
Require Import Cat.
Require Import NatTrans Func_Cat Operations.

Require Import Coq.Logic.EqdepFacts.
Import EqNotations.
Require Import Coq.Program.Equality.
Require Export ProofIrrelevance.
Require Export JMeq.
Require Import Eqdep.

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
Axiom par_eqv_def : forall a b: obj, forall f g : hom a b, HomParEqv a b f g <-> f = g.


Lemma rel_equiv : forall a b: obj, forall f g : hom a b , f = g ->
  forall (n1 : a) , forall (pf : projT1 f n1), forall (pf1 : projT1 g n1),
   (projT2 f) n1 pf = (projT2 g) n1 pf1.
Proof.
 intros a b f g h. rewrite h. intros.
 replace pf with pf1. auto. apply pf_ir.
Defined.

Lemma same_app : forall a b: obj, forall P : a -> Prop, forall f g : forall x : a, P x -> b, 
  forall (n1 n2 : a) , f = g -> n1 = n2 -> (forall (pf : P n1), forall (pf1 : P n2),
   f n1 pf = g n2 pf1).
Proof.
  intros a b P f g n1 n2 e e1.
  rewrite e. rewrite e1. intros. rewrite (pf_ir _ pf pf1). auto.
Defined.

(* composition in Par *)
Definition Compose : forall A B C : Set, hom A B -> hom B C -> hom A C.
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
  intros a b. compute. intro. destruct X.
  exists x. intros. exact x0.
Defined.


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
Instance Par_isRC : RestrictionCat Par_Cat rc_Par .
exists. Defined.

Inductive empty_set : Set := .

Inductive unit : Set :=
    tt : unit.

Definition  par_p_term : Par_isRC := unit.
Definition  par_pt_morph : ∀ (a : Par_isRC), Hom a par_p_term.
  intros. compute. destruct Par_isRC. 
  exists (fun (x : a) => True). intros; tauto.
Defined.

Definition  par_id_is_ptm : id par_p_term = par_pt_morph par_p_term .
  apply par_eqv_def. compute; split; try intros; try split; try intros; try tauto.
  destruct z. auto. 
Defined.

Definition p_m_t_prop : Prop. 
  destruct Par_isRC. destruct rc_Par. exact (∀ (a : Par_isRC), rc a par_p_term (par_pt_morph a) = id a).
Defined.

Definition  par_morph_total : p_m_t_prop.
  compute. intros. try tauto.
Defined.

Definition pmug_prop : Prop. 
  destruct Par_isRC. destruct rc_Par. 
  exact (∀ (a b : Par_isRC) (f : Hom a b), 
  ((par_pt_morph b) ∘f) = (par_pt_morph a) ∘ (rc a b f)).
Defined.

Definition  par_pt_morph_unique_greatest : pmug_prop.
  compute. intros. destruct f. apply par_eqv_def. 
  compute; split; try intros; try split; try intros; try split; try intros; try auto;
  try destruct H; auto.
  destruct pf. destruct pf1. auto.
Defined.

Definition  par_p_prod (a b : Par_isRC) : Par_isRC .
  compute. compute in a. compute in b. exact (a * b).
Defined.

Definition  par_Pi_1p (a b : Par_isRC) : Hom (par_p_prod a b) a.
  compute. exists (fun (t : a * b) => True). intros.
  exact (fst x).
Defined.

Definition  par_Pi_2p (a b : Par_isRC) : Hom (par_p_prod a b) b.
  compute. exists (fun (t : a * b) => True). intros.
  exact (snd x).
Defined.

Definition  par_Pi_1Tot_prop (a b : Par_isRC) : Prop.
  destruct Par_isRC. destruct RCat_RC. exact (rc (par_p_prod a b) a (par_Pi_1p a b) = id (par_p_prod a b)).
Defined.

Definition  par_Pi_1Tot (a b : Par_isRC) : par_Pi_1Tot_prop a b.
  compute. apply par_eqv_def. compute. split; try split; try intros; try intros; try auto.
Defined. 

Definition  par_Pi_2Tot_prop (a b : Par_isRC) : Prop.
  destruct Par_isRC. destruct RCat_RC. exact (rc (par_p_prod a b) b (par_Pi_2p a b) = id (par_p_prod a b)).
Defined.

Definition  par_Pi_2Tot (a b : Par_isRC) : par_Pi_2Tot_prop a b.
  compute. apply par_eqv_def. compute. split; try split; try intros; try intros; try auto.
Defined. 

Definition  par_pProd_morph_ex (a b : Par_isRC) : ∀ (p' : Par_isRC) (r1 : Hom p' a) (r2 : Hom p' b), Hom p' (par_p_prod a b) .
  compute. intros. destruct r1 as [r1]; destruct r2 as [r2].
  exists (fun (t : p') => (r1 t) /\ (r2 t)).
  intros. destruct H. exact ((a0 x H, b0 x H0)).
Defined.

Definition  par_pProd_morph_rest_prop (a b : Par_isRC) : Prop.
  destruct Par_isRC. destruct RCat_RC. exact (∀ (p' : Par_isRC) (r1 : Hom p' a) (r2 : Hom p' b), 
    (rc p' a r1)∘(rc p' b r2) = rc p' (par_p_prod a b) (par_pProd_morph_ex a b p' r1 r2)).
Defined. 

Definition  par_pProd_morph_rest (a b : Par_isRC) : par_pProd_morph_rest_prop a b.
  compute. intros. apply par_eqv_def. compute. destruct r1 as [r1]; destruct r2 as [r2].
  split; intros; try split; try intros; try split; try destruct H; try auto.
  destruct pf. auto.
Defined.

Definition  par_pProd_morph_com_1 (a b : Par_isRC) : ∀ (p' : Par_isRC) (r1 : Hom p' a) (r2 : Hom p' b), lt_eq p' a ((par_Pi_1p a b) ∘ (par_pProd_morph_ex a b p' r1 r2))  r1.
  compute. intros. apply par_eqv_def. compute. destruct r1 as [r1]; destruct r2 as [r2].
  intros; try intros; try split; try intros ; try split; try intros; 
  try destruct H as [h1 h2];  try split; try intros; try split; try split; try (exact (h2 h1));
  try destruct h1 as [h11 h12]; try destruct h11 as [h111 h112]; try destruct h12 as [h112 h122]; try auto.
  destruct pf. destruct pf1. destruct a2. destruct a1. rewrite (pf_ir (r1 z) (r (conj a1 t0)) r0). auto.
Defined.

Definition  par_pProd_morph_com_2 (a b : Par_isRC) : ∀ (p' : Par_isRC) (r1 : Hom p' a) (r2 : Hom p' b), lt_eq p' b ((par_Pi_2p a b) ∘ (par_pProd_morph_ex a b p' r1 r2))  r2.
  compute. intros. apply par_eqv_def. compute. destruct r1 as [r1]; destruct r2 as [r2].
  intros; try intros; try split; try intros ; try split; try intros; 
  try destruct H as [h1 h2];  try split; try intros; try split; try split; try (exact (h2 h1));
  try destruct h1 as [h11 h12]; try destruct h11 as [h111 h112]; try destruct h12 as [h112 h122]; try auto.
  destruct pf. destruct pf1. destruct a2. destruct a1. rewrite (pf_ir (r2 z) (r (conj a1 t0)) r3). auto.
Defined.

Definition  par_pProd_morph_unique_prop (a b : Par_isRC) : Prop.
    destruct Par_isRC. destruct RCat_RC. 
    exact (∀ (p' : Par_isRC) (r1 : Hom p' a) (r2 : Hom p' b) (pm : Hom p' (par_p_prod a b)),
     (lt_eq p' a ((par_Pi_1p a b) ∘ pm)  r1) -> (lt_eq p' b ((par_Pi_2p a b) ∘ pm)  r2)
       -> ((rc p' a r1)∘(rc p' b r2) = rc p' (par_p_prod a b) pm) -> pm = par_pProd_morph_ex a b p' r1 r2).
Defined.

Definition  par_pProd_morph_unique (a b : Par_isRC) : par_pProd_morph_unique_prop a b.
  unfold par_pProd_morph_unique_prop. simpl. 
  intros. apply par_eqv_def. compute.
  destruct r1 as [r1]; destruct r2 as [r2]. destruct pm.
  split; try intros; try split; try intros; try split;

  simpl in H1; simpl in H0; simpl in H;
  inversion H1. rewrite <- H4 in H2;
  destruct H2; exact (H3 H2).
  rewrite <- H4 in H2; destruct H2; try auto.
  destruct H2. split. auto. intro; auto.
  destruct pf1. compute in p.
  assert (H_f1 : (x z ∧ (x z → True)) ∧ (x z ∧ (x z → True) → r1 z)).
  split; try intros; try split; try intros; try split; try auto.
  assert (H_f2 : x z ∧ (x z → True)).
  split; try intros; try auto.
  generalize (rel_equiv _ _ _ _ H z H_f1 H_f2).
  assert (H_s1 : (x z ∧ (x z → True)) ∧ (x z ∧ (x z → True) → r2 z)).
  split; try intros; try split; try intros; try split; try auto.
  assert (H_s2 : x z ∧ (x z → True)).
  split; try intros; try auto.
  generalize (rel_equiv _ _ _ _ H0 z H_s1 H_s2).
  compute. destruct H_f1; destruct H_f2; destruct H_s1; destruct H_s2.
  replace (r4 a2) with r0; try (apply pf_ir). replace (r3 a1) with r; try (apply pf_ir). 
  replace x1 with pf; try (apply pf_ir). replace x0 with pf; try (apply pf_ir).
  destruct (p z pf). intros. rewrite H3. rewrite H6. auto.
Defined.

Definition PPTerm : @ParTerm Par_isRC rc_Par Par_isRC.
  exists par_p_term par_pt_morph.
  exact par_morph_total. exact par_id_is_ptm. exact par_pt_morph_unique_greatest.
Defined.

Definition PPProds : @Has_pProducts Par_isRC rc_Par Par_isRC.
  compute. intros. exists (par_p_prod a b) (par_Pi_1p a b)  (par_Pi_2p a b) (par_pProd_morph_ex a b).
  exact (par_Pi_1Tot a b). exact (par_Pi_2Tot a b).
  exact (par_pProd_morph_rest a b).
  exact (par_pProd_morph_com_1 a b). exact (par_pProd_morph_com_2 a b).
  exact (par_pProd_morph_unique a b).
Defined.

Instance Par_isCRC : CartRestrictionCat rc_Par .
  exists. exact PPTerm. exact PPProds. 
Defined.


(* map from objects in Set to objects in Tot(Par) *)
Definition Fo : Set_Cat -> Tot rc_Par Par_isRC.
  compute. intros. exists X. auto.
Defined. 

(* map from arrows in Set to arrows in Tot(Par) *)
Definition Fm : ∀ (a b : Set_Cat), Hom Set_Cat a b → Hom (Tot rc_Par Par_isRC) (Fo a) (Fo b).
  intros. compute.
  exists (existT (λ P : a → Prop, ∀ x : a, P x → b) 
  (λ _ : a, True) (λ (x : a) (_ : True), H x)). tauto.
Defined.

(* map from objects in Tot(Par) to objects in Set *)
Definition Fo' : Tot rc_Par Par_isRC -> Set_Cat.
  compute. intros. destruct X. exact x.
Defined. 

(* map from arrows in Tot(Par) to arrows in Set *)
Definition Fm' : ∀ (a b : (Tot rc_Par Par_isRC)), Hom (Tot rc_Par Par_isRC) a b -> Hom Set_Cat (Fo' a) (Fo' b).
  intros a b f. compute. destruct f as [fp f]. destruct a as [a]; destruct b as [b].
  destruct fp. compute in p. compute in f. intro x0. compute in x. 
  assert (pf : x x0). 
  inversion f. auto.
  exact (p x0 pf).
Defined.

(* auxiliary results about equality between existential and sigma types *)
Lemma sig_eq : forall (a b : (Tot rc_Par Par_isRC)), forall (f g : Hom (Tot rc_Par Par_isRC) a b),
  (proj1_sig f = proj1_sig g)  -> f = g.
Proof.
  intros; destruct f; destruct g. compute in H. replace x with x0.
  compute in x. destruct x. compute in x0; destruct x0. compute. inversion H.
  destruct a; destruct b.
  compute in t; compute in t0. eauto. 
Defined.

Lemma exist_eq : forall (U:Type) (P:U -> Prop) (p q:U) (x:P p) (y:P q), p = q ->
    exist P p x = exist P q y.
Proof.
  intros. apply eq_dep_eq_sig . generalize x. 
  replace (∀ x0 : P p, eq_dep U P p x0 q y) with (∀ x0 : P q, eq_dep U P q x0 q y).
  intros. rewrite (pf_ir (P q) x0 y). auto. rewrite H. auto.
Defined.

(* define functor from Set to Tot(Par) *)
Definition TotPar_Set_Cat_Eqv_f : Functor Set_Cat (Tot rc_Par Par_isRC). 
Proof.
  unfold Set_Cat. unfold Par_isRC. unfold rc_Par.
  exists Fo Fm. intros. unfold id. compute. 
  apply (sig_eq (Fo c) (Fo c) _ _ ).
  compute. auto.
  intros. compute.
  apply (sig_eq (Fo a) (Fo c) _ _ ). 
  compute. apply par_eqv_def. compute.
  split; try intros;  try auto. destruct pf1. auto.
Defined.

(* define functor from Tot(Par) to Set *)
Definition TotPar_Set_Cat_Eqv_b : Functor (Tot rc_Par Par_isRC) Set_Cat .
  exists Fo' Fm'. intros. unfold id. 
  destruct c. compute. auto.
  intros. 
  destruct a; destruct b; destruct c. 
  destruct f; destruct g. compute in x.
  destruct x3; destruct x2. 
  compute in p. compute in x2. compute in t2.
  compute in x3. compute in p0.
  compute in t3.
  inversion t2. inversion t3. 
  unfold compose. 
  apply functional_extensionality. intro. 
  simpl. compute in x4. assert (x2 x4). rewrite H0. auto.
  rewrite (pf_ir (x2 x4) _ H). 
  assert (x3 (p0 x4 H)). rewrite H2. auto.
  rewrite (pf_ir (x3 (p0 x4 H)) _ H4).
  unfold rc_ParMap. compute. 
  assert (H5' : existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) 
             (λ z : x, x2 z ∧ (∀ p1 : x2 z, x3 (p0 z p1)))
             (λ (x5 : x) (_ : x2 x5 ∧ (∀ p1 : x2 x5, x3 (p0 x5 p1))), x5) =
           existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) (λ _ : x, True) (λ (x5 : x) (_ : True), x5)).
  rewrite H2. rewrite H0. apply par_eqv_def. compute. tauto. 
  assert (H6' : existT 
                 (λ x5 : x → Prop, ∀ x6 : x, x5 x6 → x) 
                 (λ _ : x, True) 
                 (λ (x5 : x) (_ : True), x5) =
               existT 
                 (λ x5 : x → Prop, ∀ x6 : x, x5 x6 → x) 
                 (λ _ : x, True) 
                 (λ (x5 : x) (_ : True), x5)). auto.
  rewrite (pf_ir (existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) 
             (λ z : x, x2 z ∧ (∀ p1 : x2 z, x3 (p0 z p1)))
             (λ (x5 : x) (_ : x2 x5 ∧ (∀ p1 : x2 x5, x3 (p0 x5 p1))), x5) =
           existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) (λ _ : x, True) (λ (x5 : x) (_ : True), x5)) _ H5').
  inversion H5'.

  assert (existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) (λ _ : x, True) (λ (x5 : x) (_ : True), x5) =
       existT (λ P : x → Prop, ∀ x5 : x, P x5 → x) (λ _ : x, True) (λ (x5 : x) (_ : True), x5)
       → x2 x4 ∧ (∀ p1 : x2 x4, x3 (p0 x4 p1))) . 
  intro. split. auto. intro. replace p1 with H. auto. apply pf_ir.
  assert (existT (λ x5 : x → Prop, ∀ x6 : x, x5 x6 → x)
                 (λ _ : x, True) 
                 (λ (x5 : x) (_ : True), x5) =
               existT (λ x5 : x → Prop, ∀ x6 : x, x5 x6 → x)
                 (λ _ : x, True) 
                 (λ (x5 : x) (_ : True), x5)). auto.
  replace _ with (H5 H8). destruct (H5 H8). replace x5 with H. replace (x6 H) with H4.
  auto. apply pf_ir. apply pf_ir. apply pf_ir.
Defined.


(* show that composing the above functors Tot(Par) -> Set -> Tot(Par) gives the identity functor on Tot(Par)
  by showing it's equal to the identity func on objects and maps *)
Lemma TotPar_Set_Cat_Eqv_o : forall a ,
 @FO (Tot rc_Par Par_isRC) (Tot rc_Par Par_isRC)
  (Functor_compose  TotPar_Set_Cat_Eqv_b TotPar_Set_Cat_Eqv_f) a = @FO (Tot rc_Par Par_isRC) (Tot rc_Par Par_isRC) (Functor_id _) a.
compute. intros. destruct a.  auto.
Defined.

Definition TotPar_Set_Cat_Eqv_m (a b : (Tot rc_Par Par_isRC)) (f : @Hom  (Tot rc_Par Par_isRC) a b) (x : (proj1_sig a)) :
 (@FA (Tot rc_Par Par_isRC) (Tot rc_Par Par_isRC) (Functor_id _) _ _ f = 
    (@FA (Tot rc_Par Par_isRC) (Tot rc_Par Par_isRC) (Functor_compose  TotPar_Set_Cat_Eqv_b TotPar_Set_Cat_Eqv_f) _ _ f)).
destruct f as [f]. destruct a as [a]. destruct b as [b]. compute.
apply exist_eq. compute in f. destruct f as [pf f].
apply par_eqv_def. simpl. split. compute in t. inversion t. 
intros. split; auto. intros. compute.
assert (forall (pff : (pf z)), f z pf0 = f z pff).
intros. rewrite (pf_ir (pf z) pf0 pff). auto. apply H0.
Defined.

(* show that composing the above functors Set -> Tot(Par) -> Set gives the identity functor on Set 
    by showing it's equal to the identity func on objects and maps *)
Lemma Set_TotPar_Cat_Eqv_o : forall a ,
 @FO Set_Cat Set_Cat
  (Functor_compose  TotPar_Set_Cat_Eqv_f TotPar_Set_Cat_Eqv_b) a = @FO Set_Cat Set_Cat (Functor_id _) a.
compute.  auto.
Defined.

Definition Set_TotPar_Cat_Eqv_m (a b : Set_Cat) (f : @Hom Set_Cat a b) (x : a) :
 (@FA Set_Cat Set_Cat (Functor_id _) _ _ f = 
    (@FA Set_Cat Set_Cat (Functor_compose  TotPar_Set_Cat_Eqv_f TotPar_Set_Cat_Eqv_b ) _ _ f)).
compute. apply functional_extensionality. intro. auto.
Defined.


(* define the range combinator in a cartesian restriction category *)
Definition rrc : rrcType Par_isRC.
  unfold rrcType. intros. destruct X as [fp f]. compute.
  exists (fun (y : b) => (exists x : a, exists p : (fp x), f x p = y)).
  intros. exact x.
Defined.

Definition rrc_Par :  @RangeComb Par_isCRC rc_Par Par_isCRC.
  exists rrc; intros; destruct f; apply par_eqv_def; try destruct g;  compute  ;
  try split; try intros; try split; 
  try split; try intros; try split; try auto; try destruct H; try auto.
  exists z. exists p. auto. destruct pf.
  rewrite (pf_ir _ x0 pf1); auto.
  exists x1. destruct H. destruct x2. exists x2. auto.
  destruct H. destruct x2. generalize (x3 x2). intro.
  rewrite H in H0. auto. 
  destruct H as [x' p]. destruct p as [p e].
  exists x'. assert (x x' ∧ (∀ p0 : x x', x0 (b0 x' p0))).
  split. exact p. intro. rewrite (pf_ir _ p p0) in e.
  rewrite e.
  assert ((∃ (x0 : a) (p : x x0), b0 x0 p = z)).
  exists x'. exists p. rewrite (pf_ir _ p p0). auto.
  exact (H0 H). exists H. destruct H. 
  rewrite (pf_ir _ x1 p); auto.
  destruct pf1. auto.
  destruct H. destruct x2. destruct e. 
  exists x3.  assert (x x3 ∧ (∀ p : x x3, x0 (b0 x3 p))).
  split. destruct e. exact x4. intros.
  destruct e. rewrite (pf_ir _ p x4). rewrite e.
  apply x2. exists x3. exists x4. auto.
  exists H0. destruct H0. 
  destruct e. rewrite (pf_ir _ x4 x6).
  elim H. rewrite (same_app _ _ _ c0 c0 (b0 x3 x6) x1 eq_refl e (x5 x6) (x2
     (ex_intro (λ x7 : a, ∃ p : x x7, b0 x7 p = x1) x3
        (ex_intro (λ p : x x3, b0 x3 p = x1) x6 e)))). auto.
  destruct H. destruct x2.
  exists (b0 x1 x2).
  assert ((∃ (x4 : a) (p : x x4), b0 x4 p = b0 x1 x2) ∧ ((∃ (x4 : a) (p : x x4), b0 x4 p = b0 x1 x2) → x0 (b0 x1 x2))).
  split.  exists x1. exists x2. auto.
  intro. exact (x3 x2). exists H0.
  destruct H0. rewrite <- H.
  rewrite (pf_ir _ (x4 e) (x3 x2)). auto. 
Defined.


Definition Par_isRangeC : RangeCat Par_isCRC rc_Par Par_isCRC rrc_Par.
exists. Defined.

Definition Par_BCC : @sat_Beck_Chevalley Par_isCRC rc_Par Par_isCRC Par_isCRC rrc_Par Par_isRangeC .
unfold sat_Beck_Chevalley. 
unfold Beck_Chevalley. intros.
apply par_eqv_def. unfold HomParEqv. simpl.
unfold rrc. destruct f as [pf f]. destruct g as [pg g].
simpl. split; try intros; try split; try intros; try split; try split; try auto; try intros;
try (destruct H). destruct z as [y1 y1']. destruct x0 as  [x1 x1']; destruct H; compute.
compute in H; destruct x0. destruct a;  destruct a0; compute in H.
exists x1. exists (p0 t).
assert (fst (f x1 (p0 t), g x1' (p1 t0)) = fst (y1, y1')).
rewrite H. auto. compute in H0. auto.
destruct z as [y1 y1']. destruct x0 as  [x1 x1']; destruct H; compute.
compute in H; destruct x0. destruct a;  destruct a0; compute in H.
assert (snd (f x1 (p0 t), g x1' (p1 t0)) = snd (y1, y1')).
rewrite H. auto. compute in H0. exists x1'. exists (p1 t0). auto.
destruct z as [y1 y1']. unfold par_p_prod.  destruct H; compute.
destruct H0. destruct (H1 I). destruct (H2 I).
destruct H3; destruct H4. exists ( x0 , x1).
assert (p : (True ∧ (True → pf (let (fst, _) := (x0, x1) in fst)))
    ∧ True ∧ (True → pg (let (_, snd) := (x0, x1) in snd))).
split; try split; try auto. exists p. destruct p. destruct a. destruct a0.
compute in H3. compute in H4. 
rewrite <- H3. rewrite <- H4. assert (p t= x2). apply pf_ir; auto.
assert (p0 t0 = x3). apply pf_ir; auto. rewrite H5; rewrite H6; auto.
destruct z as [z1 z2]. destruct H. destruct pf1.
destruct a. destruct a0. compute. auto. 
Defined.

Instance Par_isCRRC : CartRangeCat Par_isCRC rc_Par Par_isCRC Par_isCRC rrc_Par Par_isRangeC.
exists.
exact Par_BCC.
Defined.
