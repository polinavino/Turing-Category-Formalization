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

Require Import Main_Category.
Require Import CCC.
Require Import Coq.Setoids.Setoid.


Require Import Coq.Logic.EqdepFacts.
Import EqNotations.
Require Import Coq.Program.Equality.
Require Export ProofIrrelevance.
Require Export JMeq.
Require Import Eqdep.

Generalizable All Variables. 

(*AXIOM proof irrelevance*)
Axiom pf_ir : forall A: Prop , forall p q:A, p=q.

Lemma idUniqueR `(C : Category) : forall (a : C), forall id1 : Hom a a, 
    (forall b : C, forall f : Hom a b, f  ∘id1 = f) -> id1 = id a.
Proof.
  intros. destruct (H a (id a)). simpl. rewrite (id_unit_left a a id1). auto.
Defined.

Lemma idUniqueL `(C : Category) : forall (b : C), forall id1 : Hom b b, 
    (forall a : C, forall f : Hom a b, id1 ∘f = f) -> id1 = id b.
Proof.
  intros. destruct (H b (id b)). simpl. rewrite (id_unit_right b b id1). auto.
Defined.

(* exists-rewriting lemma *)
Lemma exist_eq : forall (U:Type) (P:U -> Prop) (p q:U) (x:P p) (y:P q), p = q ->
    exist P p x = exist P q y.
Proof.
  intros. apply eq_dep_eq_sig . generalize x. 
  replace (∀ x0 : P p, eq_dep U P p x0 q y) with (∀ x0 : P q, eq_dep U P q x0 q y).
  intros. rewrite (pf_ir (P q) x0 y). auto. rewrite H. auto.
Defined.

(* Type of a restriction combinator *)
Definition rcType (C : Category): Type.
  exact (forall a b : C, @Hom C a b -> @Hom C a a ).
Defined.


(* Restriction Combinator definition *)
Class RestrictionComb `(C : Category) : Type :=
{

    rc : rcType C
  ; rc1             : forall (a b : Obj), forall (f : Hom a b), f ∘(rc a b f)= f 
  ; rc2             : forall (a b c: Obj), forall (f : Hom a b)`(g : Hom a c), (rc a c  g ) ∘(rc a b f ) = (rc a b  f ) ∘ (rc a c  g )
  ; rc3             : forall (a b c: Obj), forall (f : Hom a b)`(g : Hom a c), rc a c (g ∘(rc a b f) )  =  (rc a c g ) ∘ (rc a b f )
  ; rc4             : forall (a b c: Obj), forall (f : Hom a b)`(g : Hom b c), (rc b c g) ∘f = f ∘(rc a c (g ∘f))    

}.


Coercion rc : RestrictionComb >-> rcType.

(* proof of rc_d from rc1...rc4 rules *)
Lemma rc_d_pf : forall (C : Category), forall RC : RestrictionComb C, forall (a b c: Obj), forall (f : Hom a b), forall (g : Hom b c), rc a c (compose f g) = rc a b (compose f (rc b c g) ).
Proof.
  intros. destruct C; destruct RC. compute.
  compute in rc8. rewrite rc8. compute in rc7. rewrite rc7.
  compute in rc6. rewrite rc6. rewrite <- rc7.
  compute in rc5. rewrite assoc.
  replace ((compose a a b (rc0 a b f) f)) with f. 
  auto. apply symmetry. exact (rc5 _ _ f).
Defined.


(* Restriction category *)
Class RestrictionCat (C : Category)  (rc : RestrictionComb C) : Type :=
{
  RCat_RC : RestrictionComb C := rc
  ; rc_d := rc_d_pf C RCat_RC
}.

Instance RestrictionCatsAreCategories `{ RC: RestrictionCat  }  : Category := C.

Coercion RestrictionCatsAreCategories : RestrictionCat >-> Category.

(*
Lemma idem_comp (C : Category) (rc : @RestrictionComb C) (RC : @RestrictionCat C rc) : forall
  (a : RC) (e e' : Hom a a) (pe : e ∘ e = e) (pe' : e' ∘ e' = e'), (e ∘ e') ∘ (e ∘ e') = e ∘ e'.
Proof.
  intros. rewrite assoc. rewrite pe.
*)

(* restriction idempotents closed under composition *)
Lemma r_idem_comp `{RC : RestrictionCat}
  (a : RC) (e e' : Hom a a) (pe : (rc a a e) = e) (pe' : (rc a a e') = e') : (rc a a (e ∘ e')) = e ∘ e'.
Proof.
  destruct RC. destruct rc0. destruct C. transitivity (rc0 a a (e ∘ (rc0 _ _ e'))). 
  compute. compute in pe'. rewrite pe'. auto.
  compute in rc7. compute. rewrite (rc7 _ _ _ e' e).
  compute in pe. compute in pe'. rewrite pe. rewrite pe'. auto.
Defined.

(* id is a total map *)
Definition IdIsTotal `{RC : RestrictionCat} : ∀ a : C, rc _ _ (id a) = id a.
  intro; destruct C;  destruct RC; destruct rc0; compute.
  rewrite <- (id_unit_left a a (rc0 a a (id a))).
  compute in rc5.
  rewrite (rc5 a a (id a)).
  reflexivity.
Defined.

(* X is a retract of Y when *)
Definition isRetractOf `{C : Category} : Obj -> Obj -> Prop.
  intros x y.
  exact (exists m : Hom x y, exists r : Hom y x, r ∘m = id x).
Defined.


(* in an embedding-retraction pair (m, r), m is a total map *)
Lemma mIsTotal `{RC : RestrictionCat} : forall ( x y : RC), forall (m : Hom x y), forall (r : Hom y x), (r ∘m = id x) -> (rc _ _ m = id x).
Proof.
  intros. compute in H.
  destruct C; destruct RC; destruct rc0. compute.
  compute in rc5. rewrite <- H.
  replace (compose x y x m r) with (compose x y x (compose x x y (rc0 x y m) m) r).
  apply symmetry. rewrite <- assoc.
  rewrite H. rewrite id_unit_left; auto.
  rewrite (rc5 _ _ m). auto.
Defined.

(* Collection of total maps in a restriciton category - all maps such that their restriction is the identity map *)
Definition TotMaps `{C : Category} `(rc : @RestrictionComb C) (RC : RestrictionCat C rc) : ∀ a b, Hom a b → Prop.
  destruct RC.
  destruct rc.
  intros a b f.
  exact (rc0 a b f = id a).
Defined.


(* A subcategory of a restriction category with the same objects as the restriction category and only the total maps *)
Definition Tot `{C : Category} `(rc : @RestrictionComb C) : RestrictionCat C rc -> Category.
  intros R. 
  apply (Wide_SubCategory C (TotMaps rc R)); destruct C; destruct R; destruct rc; intros; unfold TotMaps; compute.
 
(* id is total *)
  rewrite <- (id_unit_left a a (rc0 a a (id a))).
  compute in rc5.
  rewrite (rc5 a a (id a)).
  reflexivity.

(* composition of total maps is total *)

  unfold TotMaps in H.
  unfold TotMaps in H0.
  compute in rc_d0.
  rewrite (rc_d0 a b c f g).
  rewrite H0.
  simpl.
  rewrite (id_unit_left a b f).
  rewrite H.
  auto.
Defined.


(*define restriction combinator in a total subcategory *)
Lemma rct `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) : ∀ a b : Tot rc RC, Category.Hom a b → Category.Hom a a.
Proof.
  destruct C.
  destruct RC.
  intros a b f.
  destruct f as [f fP]; destruct rc.
  compute in fP; compute in f.
  destruct a as [a a1]; destruct b as [b b1].
  compute.
  exists (rc0 a b f).
  rewrite fP.
  rewrite <- (id_unit_left a a (rc0 a a (id a))).
  compute in rc5.
  rewrite (rc5 a a (id a)).
  reflexivity.
Defined.



(* definition of a restriction combinator in the total subcategory of a restriction category *)
Lemma rc_in_tot `{C : Category} `(rc : @RestrictionComb C) : forall RC : RestrictionCat C rc, RestrictionComb (Tot rc RC).
Proof.
  destruct C. intro. 
  exists (rct rc RC); intros; destruct rc ; unfold rct; apply proof_irrelevance.
Defined.


Instance makeRC `{C : Category} (r : @RestrictionComb C) : RestrictionCat C r := {}.


(* Total Subcategory of a restriction category is a restriction category in a trivial way *)
Definition TotR `{C : Category} `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) := makeRC (rc_in_tot rc RC).


(* map ordering based on their restrictions *)
Definition lt_eq `{RC : RestrictionCat} (a b : RC) (f g : Hom a b) : Prop.
  destruct C; destruct RC; destruct RCat_RC0.
  exact (g ∘(rc a b f) = f).
Defined.


(* consider total subcategory object a as an object of to full restriction category *)
Definition fc `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} (a : TotR rc RC) : RC.
  destruct C; destruct RC; destruct a.
  compute in x.
  compute.
  exact x.
Defined.

(* consider total subcategory object a as an object of to full restriction category *)
Definition sc `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} (a : RC) : TotR rc RC.
  destruct C ; destruct RC. compute in a.
  compute.
  exists a; auto.
Defined.

(* define the partial (restriction) product in a restriction category *)
Class ParProd `{RC : RestrictionCat} (a b : RC)  : Type :=
{
  p_prod : RC ;

  Pi_1p : Hom p_prod a ;

  Pi_2p : Hom p_prod b ;

  Pi_1Tot : rc _ _ Pi_1p = id p_prod ; 

  Pi_2Tot : rc _ _ Pi_2p = id p_prod ;

  pProd_morph_ex : ∀ (p' : RC) (r1 : Hom p' a) (r2 : Hom p' b), Hom p' p_prod ;

  pProd_morph_rest : ∀ (p' : RC) (r1 : Hom p' a) (r2 : Hom p' b), (rc  p' a r1)∘(rc p' b r2) = rc p' p_prod (pProd_morph_ex p' r1 r2) ; 

  pProd_morph_com_1 : ∀ (p' : RC) (r1 : Hom p' a) (r2 : Hom p' b), lt_eq _ _ (Pi_1p ∘ (pProd_morph_ex p' r1 r2))  r1;
  
  pProd_morph_com_2 : ∀ (p' : RC) (r1 : Hom p' a) (r2 : Hom p' b), lt_eq _ _  (Pi_2p ∘ (pProd_morph_ex p' r1 r2))  r2  ;
  
  pProd_morph_unique : ∀ (p' : RC) (r1 : Hom p' a) (r2 : Hom p' b) (pm : Hom p' p_prod), (lt_eq _ _ (Pi_1p ∘ pm)  r1) -> (lt_eq _ _ (Pi_2p ∘ pm)  r2)
       -> ((rc  p' a r1)∘(rc p' b r2) = rc p' p_prod pm) -> pm = pProd_morph_ex _ r1 r2
}.


Coercion p_prod : ParProd >-> Obj.


Definition Has_pProducts `{RC : RestrictionCat }  : Type := ∀ a b, ParProd a b.

(*
Definition Has_pProducts `(C : Category)  `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) : Type := ∀ a b, ParProd a b.
*)

(* define total projection maps in a total subcategory of a cartesian restriciton category *)
Definition Pi_1map `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), Hom (sc rc aXPb) a.
  destruct (TotR rc RC).
  destruct aXPb as [aXPb]. 
  destruct C; destruct RC. destruct rc.
  compute in Pi_1p0. compute.
  exists Pi_1p0. exact Pi_1Tot0.
Defined.

Definition Pi_2map `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), Hom (sc rc aXPb) b.
  destruct (TotR rc RC).
  destruct aXPb as [aXPb]. 
  destruct C; destruct RC. destruct rc.
  compute in Pi_2p0. compute.
  exists Pi_2p0. exact Pi_2Tot0.
Defined.


(* define total unique product map in a total subcategory of a cartesian retriction category *)
Definition Prod_morphs `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), (∀ (p : TotR rc RC) (r1 : Hom p a) (r2 : Hom p b), Hom p (sc rc aXPb)).
  destruct aXPb as [aXPb]; destruct (TotR rc RC); intros; simpl.
  intros. compute. compute in pProd_morph_ex0.
  destruct C; destruct RC. compute in r1; compute in r2.
  exists ( pProd_morph_ex0 (fc rc p) (proj1_sig r1) (proj1_sig r2)).
  destruct rc. compute.
  destruct p. compute in pProd_morph_rest0.
  destruct r1 as [r1]; destruct r2 as [r2].
  destruct a as [a]; destruct b as [b].
  generalize (pProd_morph_rest0 x r1 r2); intro pmr.
  rewrite e in pmr; rewrite e0 in pmr. rewrite id_unit_left in pmr. auto.
Defined.


(* define products in a total subcategory of a restriction category *)
Definition defProdInTot `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), (Product a b).
  intros.

  exists (sc rc aXPb) (Pi_1map rc a b aXPb) (Pi_2map rc a b aXPb) (Prod_morphs rc a b aXPb); 
  destruct (TotR rc RC);
  destruct C; destruct RC; destruct rc;
  destruct r1 as [r1]; destruct r2 as [r2]; destruct a as [a]; destruct b as [b];
  destruct aXPb as [aXPb];  destruct p' as [p];
  unfold Pi_2map ; simpl. unfold Prod_morphs; intros.
  assert (assr1 : (compose p aXPb a (pProd_morph_ex0 p r1 r2) Pi_1p0) = r1). 
  compute in pProd_morph_com_3. rewrite <- pProd_morph_com_3.
  compute in rc_d1; rewrite rc_d1. compute in Pi_1Tot0. rewrite Pi_1Tot0.
  rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  compute in t; compute in t0; rewrite t; rewrite t0.
  rewrite id_unit_left. rewrite id_unit_right. auto.
  apply pf_ir.

  assert (assr2 : (compose p aXPb b (pProd_morph_ex0 p r1 r2) Pi_2p0) = r2). 
  compute in pProd_morph_com_4. rewrite <- pProd_morph_com_4.
  compute in rc_d1; rewrite rc_d1. compute in Pi_2Tot0. rewrite Pi_2Tot0.
  rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  compute in t; compute in t0; rewrite t; rewrite t0.
  rewrite id_unit_left. rewrite id_unit_right. auto.
  apply pf_ir.

  assert (sigeq1 : forall (v w : {f0 : Hom p b | rc0 p b f0 = id p}), forall (f g : Hom p b), v = w -> proj1_sig v = f -> proj1_sig w = g -> f=g).
  intros. rewrite H in H0. rewrite <- H0; rewrite <- H1. auto. 
  assert (sigeq2 : forall (v w : {f0 : Hom p a | rc0 p a f0 = id p}), forall (f g : Hom p a), v = w -> proj1_sig v = f -> proj1_sig w = g -> f=g).
  intros. rewrite H in H0. rewrite <- H0; rewrite <- H1. auto. 

  intros. compute in f; compute in g. destruct f as [f]; destruct g as [g].
  compute in H; compute in H0; compute in H1; compute in H2.
  assert (fg : f = g).
  compute in pProd_morph_ex0.
  transitivity (pProd_morph_ex0 _ r1 r2).
  apply (pProd_morph_unique0).
  simpl. compute in rc_d1; rewrite rc_d1.
  compute in Pi_1Tot0; rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite e. rewrite id_unit_right. 
  apply symmetry. apply (sigeq2 _ _ (compose p aXPb a f Pi_1p0) r1 H). simpl. auto.
  simpl. auto. 
  simpl. compute in rc_d1; rewrite rc_d1.
  compute in Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite e. rewrite id_unit_right. 
  apply symmetry. apply (sigeq1 _ _ (compose p aXPb b f Pi_2p0) r2 H0). simpl. auto.
  simpl. auto.
  simpl.
  rewrite e. compute in t. rewrite t. compute in t0. rewrite t0.
  rewrite id_unit_left. auto.

  apply symmetry. apply (pProd_morph_unique0).
  simpl. compute in rc_d1; rewrite rc_d1.
  compute in Pi_1Tot0; rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite e0. rewrite id_unit_right. 
  apply symmetry. apply (sigeq2 _ _ (compose p aXPb a g Pi_1p0) r1 H1). simpl. auto.
  simpl. auto. 
  simpl. compute in rc_d1; rewrite rc_d1.
  compute in Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite e0. rewrite id_unit_right. 
  apply symmetry. apply (sigeq1 _ _ (compose p aXPb b g Pi_2p0) r2 H2). simpl. auto.
  simpl. auto.
  simpl.
  rewrite e0. compute in t. rewrite t. compute in t0. rewrite t0.
  rewrite id_unit_left. auto.
  apply pf_ir.
Defined.


(* a partial product in a restriction category is a total product in its total subcategory *)
Lemma pp_isProdInTot `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), exists (aXb : Product a b), sc rc aXPb = aXb.
Proof.
  intros.
  exists (defProdInTot rc a b aXPb).
  destruct C; destruct RC; compute. auto.
Defined.

  

(* Restriction terminal Object *)
Class ParTerm `{RC : RestrictionCat} : Type :=
{
  p_term : RC;
  pt_morph : ∀ (a : Obj), Hom a p_term;
  morph_total : ∀ (a : Obj), rc _ _ (pt_morph a) = id a;
  id_is_ptm : id p_term = pt_morph p_term ;
  pt_morph_unique_greatest : ∀ (a b : Obj) (f : Hom a b), ((pt_morph b) ∘f) = (pt_morph a) ∘rc _ _ f
}.

Coercion p_term : ParTerm >-> Obj.

(* a partial terminal object in a restriction category is a terminal object in its total subcategory *)
Definition defTermInTot `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : 
   forall t : ParTerm , Terminal (TotR rc RC).
  intros. destruct t. exists (sc rc p_term0);
  destruct RC ; destruct C; destruct rc; simpl; intros.
  exists (pt_morph0 (proj1_sig d)).
  simpl in morph_total0.
  apply (morph_total0 (proj1_sig d)).
  destruct f as [f]; destruct g as [g]. 
  assert (f = pt_morph0 (proj1_sig d)). simpl in pt_morph_unique_greatest0.
  generalize ( pt_morph_unique_greatest0 (proj1_sig d) p_term0 f); intro.
  simpl in morph_total0. rewrite e in H. rewrite id_unit_right in H.
  rewrite <- H. rewrite <- id_is_ptm0. simpl. rewrite id_unit_left. auto.
  assert (g = pt_morph0 (proj1_sig d)). simpl in pt_morph_unique_greatest0.
  generalize ( pt_morph_unique_greatest0 (proj1_sig d) p_term0 g); intro.
  simpl in morph_total0. rewrite e0 in H0. rewrite id_unit_right in H0.
  rewrite <- H0. rewrite <- id_is_ptm0. simpl. rewrite id_unit_left. auto.
  assert (f = g). rewrite H; rewrite H0. auto.
  apply pf_ir.
Defined.


(* a restriction category with a restriction terminal object and restriction products is a Cartesian restriction category *)
Class CartRestrictionCat `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : Type :=
{
  RCat_term : ParTerm ;
  RCat_HP : Has_pProducts 
}.


Instance CartRestrictionCatsAreCategories `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) `(CRC : @CartRestrictionCat C rc RC)  : RestrictionCat C rc := RC.

Coercion CartRestrictionCatsAreCategories : CartRestrictionCat >-> RestrictionCat.


(* point map - a total map with terminal object as source *)
Definition point `{C : Category} `(rco : @RestrictionComb C) `{RC : @RestrictionCat C rco}
  `{CRC : @CartRestrictionCat RC rco RC} (a : CRC) := { p : Hom (RCat_term) a | rc _ _ p = id _ }.

(*AXIOM Kleene equality *)
Definition Kl_eq `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}
  `{CRC : @CartRestrictionCat RC rc RC} (a b : CRC) (f g : Hom a b) := 
(forall  (p : point rc a) , f ∘ (proj1_sig p) = g ∘ (proj1_sig p)) . 

(* extensionality in CRCs *)
Definition is_ext `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}
  `{CRC : @CartRestrictionCat RC rc RC}  := forall (a b : CRC) (f g : Hom a b), ( Kl_eq rc a b f g <-> f = g ).


(* in a CRC, X x 1 and 1 x X are isomorphic to X *)
Lemma xX1and1XxIsox `(CRC : CartRestrictionCat ) : forall (x : C), forall ( ptrm : ParTerm  ), (forall (xX1 : ParProd x ptrm), 
   id xX1 = pProd_morph_ex x (id x) (pt_morph x)  ∘Pi_1p /\  id x = Pi_1p ∘pProd_morph_ex x (id x) (pt_morph x))  /\
   (forall (tXx : ParProd ptrm x), 
   id tXx = pProd_morph_ex x (pt_morph x) (id x)  ∘Pi_2p /\  id x = Pi_2p ∘pProd_morph_ex x  (pt_morph x) (id x) ) .
Proof.
  destruct C; destruct rc0; destruct RC; split; intros;
  split; try (destruct xX1); try (destruct tXx); destruct ptrm; generalize (IdIsTotal x) ; compute; intros IdT.
  generalize (IdIsTotal p_prod0) ; compute; intros IdTpr.

(* id xX1 and map to x *)
  compute in pProd_morph_unique0.
  assert (c1 : compose p_prod0 p_prod0 x (rc0 p_prod0 x (compose p_prod0 p_prod0 x 
      (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))
         Pi_1p0)) Pi_1p0 =  compose p_prod0 p_prod0 x 
          (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))
             Pi_1p0 ).

  compute in rc_d0. rewrite rc_d0.
  compute in  Pi_1Tot0; rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite rc_d0. compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x (id x) (pt_morph0 x)).
  rewrite IdT. rewrite id_unit_left.
  compute in morph_total0; rewrite morph_total0. rewrite id_unit_left.
  compute in Pi_1Tot0; rewrite Pi_1Tot0; rewrite id_unit_right.
  compute in pProd_morph_com_3. generalize ( pProd_morph_com_3 x (id x) (pt_morph0 x)); intro.
  rewrite <- assoc.
  rewrite <- H.
  rewrite id_unit_left. rewrite rc_d0. rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite <- ( pProd_morph_rest0 x (id x) (pt_morph0 x)).
  rewrite IdT. rewrite id_unit_left. rewrite morph_total0. rewrite id_unit_left; auto.

  assert (c2 : compose p_prod0 p_prod0 p_term0 (rc0 p_prod0 p_term0 (compose p_prod0 p_prod0 p_term0 
        (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))
      Pi_2p0)) (pt_morph0 p_prod0) =
                        compose p_prod0 p_prod0 p_term0 
        (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))
         Pi_2p0 ).
  compute in rc_d0. rewrite rc_d0.
  compute in  Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite rc_d0. compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x (id x) (pt_morph0 x)).
  rewrite IdT. rewrite id_unit_left.
  compute in morph_total0; rewrite morph_total0. rewrite id_unit_left.
  compute in Pi_1Tot0; rewrite Pi_1Tot0; rewrite id_unit_right.
  compute in pProd_morph_com_4. generalize ( pProd_morph_com_4 x (id x) (pt_morph0 x)); intro.
  rewrite <- assoc.
  rewrite <- H.
  rewrite rc_d0. rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite <- ( pProd_morph_rest0 x (id x) (pt_morph0 x)).
  rewrite IdT. rewrite id_unit_left. rewrite morph_total0. rewrite id_unit_right.
  compute in pt_morph_unique_greatest0.
  apply symmetry. rewrite <- id_unit_right.
  compute in  Pi_1Tot0; rewrite <- Pi_1Tot0. 
  rewrite <- (pt_morph_unique_greatest0 p_prod0 x Pi_1p0). auto.

  assert (c3 : compose p_prod0 p_prod0 p_prod0 (rc0 p_prod0 p_term0 (pt_morph0 p_prod0)) (rc0 p_prod0 x Pi_1p0) = rc0 p_prod0 p_prod0 
    (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))  ).
  compute in rc_d0. rewrite rc_d0. 
  compute in  Pi_1Tot0; rewrite Pi_1Tot0. rewrite id_unit_left.
  compute in morph_total0; rewrite morph_total0. 
  compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x (id x) (pt_morph0 x)).
  rewrite IdT; rewrite id_unit_left. rewrite morph_total0. rewrite id_unit_left.
  rewrite Pi_1Tot0. auto.

  rewrite (pProd_morph_unique0 p_prod0 Pi_1p0 (pt_morph0 p_prod0)
                    (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x))) c1 c2 c3 ).

  assert (c4 : compose p_prod0 p_prod0 x (rc0 p_prod0 x (compose p_prod0 p_prod0 x 
     (id p_prod0)
         Pi_1p0)) Pi_1p0 =  compose p_prod0 p_prod0 x 
          (id p_prod0) Pi_1p0 ).
  rewrite id_unit_right.   compute in  Pi_1Tot0; rewrite Pi_1Tot0.   rewrite id_unit_right; auto.

  assert (c5 : compose p_prod0 p_prod0 p_term0 (rc0 p_prod0 p_term0 (compose p_prod0 p_prod0 p_term0 
       (id p_prod0) Pi_2p0)) (pt_morph0 p_prod0) =
                        compose p_prod0 p_prod0 p_term0  (id p_prod0)  Pi_2p0 ).
  rewrite id_unit_right.   compute in  Pi_2Tot0; rewrite Pi_2Tot0.   rewrite id_unit_right.
  compute in pt_morph_unique_greatest0. 
  apply symmetry. rewrite <- id_unit_right.
  compute in Pi_2Tot0; rewrite <- Pi_2Tot0.
  apply symmetry. rewrite <- id_unit_left.
  compute in id_is_ptm0; rewrite id_is_ptm0. 
  rewrite <- (pt_morph_unique_greatest0 ). auto.


  assert (c6 : compose p_prod0 p_prod0 p_prod0 (rc0 p_prod0 p_term0 (pt_morph0 p_prod0)) (rc0 p_prod0 x Pi_1p0) = rc0 p_prod0 p_prod0 
    (id p_prod0) ).
  compute in  Pi_1Tot0; rewrite Pi_1Tot0. rewrite IdTpr.
  rewrite id_unit_left.  compute in morph_total0; rewrite morph_total0. auto. 

  rewrite (pProd_morph_unique0  p_prod0 (Pi_1p0) (pt_morph0 p_prod0)
    (id p_prod0) c4 c5 c6 ); auto.


(* id x and map to xX1 *)
  generalize (pProd_morph_rest0 x (id x) (pt_morph0 x)); compute; intro. compute in pt_morph0.
  compute in pProd_morph_com_3. generalize ( pProd_morph_com_3 x (id x) (pt_morph0 x)); intro.
  compute in morph_total0. rewrite (morph_total0 x) in H.
  rewrite IdT in H; rewrite id_unit_left in H.
  rewrite <- H0; rewrite id_unit_left .
  compute in rc_d0. rewrite rc_d0.
  compute in Pi_1Tot0;  rewrite Pi_1Tot0. 
  rewrite rc_d0.
  generalize (IdIsTotal p_prod0) ; compute; intros IdTpr; rewrite IdTpr. rewrite id_unit_left; auto.

(* id tXx and map to x *)
  compute in pProd_morph_unique0.
  assert (c1 : compose p_prod0 p_prod0 p_term0 (rc0 p_prod0 p_term0 (compose p_prod0 p_prod0 p_term0 
      (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x)))
         Pi_1p0)) (pt_morph0 p_prod0) =  compose p_prod0 p_prod0 p_term0 
          (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x)))
             Pi_1p0 ).

  compute in rc_d0. rewrite rc_d0.
  compute in  Pi_1Tot0; rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite rc_d0. compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x  (pt_morph0 x) (id x)).
  rewrite IdT. rewrite id_unit_right.
  compute in morph_total0; rewrite morph_total0. rewrite id_unit_left.
  compute in Pi_2Tot0; rewrite Pi_2Tot0; rewrite id_unit_right.
  compute in pProd_morph_com_3. generalize ( pProd_morph_com_3 x  (pt_morph0 x) (id x)); intro.
  rewrite <- assoc.
  rewrite <- H.
  rewrite rc_d0. rewrite Pi_1Tot0. rewrite id_unit_left.
  rewrite <- ( pProd_morph_rest0 x (pt_morph0 x) (id x)).
  rewrite IdT. rewrite id_unit_right. rewrite morph_total0. rewrite id_unit_right.
  compute in pt_morph_unique_greatest0.
  apply symmetry. rewrite <- id_unit_right.
  compute in  Pi_2Tot0; rewrite <- Pi_2Tot0. 
  rewrite <- (pt_morph_unique_greatest0 p_prod0 x Pi_2p0). auto.

  assert (c2 : compose p_prod0 p_prod0 x (rc0 p_prod0 x (compose p_prod0 p_prod0 x 
      (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x)))
         Pi_2p0)) Pi_2p0 =  compose p_prod0 p_prod0 x 
          (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x)))
             Pi_2p0 ).

  compute in rc_d0. rewrite rc_d0.
  compute in  Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite rc_d0. compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x (pt_morph0 x) (id x) ).
  rewrite IdT. rewrite id_unit_right.
  compute in morph_total0; rewrite morph_total0. rewrite id_unit_left.
  rewrite Pi_2Tot0; rewrite id_unit_right.
  compute in pProd_morph_com_4. generalize ( pProd_morph_com_4 x  (pt_morph0 x) (id x)); intro.
  rewrite <- assoc.
  rewrite <- H.
  rewrite id_unit_left. rewrite rc_d0. rewrite Pi_2Tot0. rewrite id_unit_left.
  rewrite <- ( pProd_morph_rest0 x (pt_morph0 x) (id x) ).
  rewrite IdT. rewrite id_unit_right. rewrite morph_total0. rewrite id_unit_left; auto.


  assert (c3 : compose p_prod0 p_prod0 p_prod0 (rc0 p_prod0 x Pi_2p0) (rc0 p_prod0 p_term0 (pt_morph0 p_prod0)) = rc0 p_prod0 p_prod0 
    (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x)))  ).
  compute in rc_d0. rewrite rc_d0. 
  compute in  Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_right.
  compute in morph_total0; rewrite morph_total0. 
  compute in pProd_morph_rest0; rewrite <- ( pProd_morph_rest0 x (pt_morph0 x) (id x) ).
  rewrite IdT; rewrite id_unit_right. rewrite morph_total0. rewrite id_unit_left.
  rewrite Pi_2Tot0. auto.

  rewrite (pProd_morph_unique0 p_prod0  (pt_morph0 p_prod0) Pi_2p0
                    (compose p_prod0 x p_prod0 Pi_2p0 (pProd_morph_ex0 x (pt_morph0 x) (id x))) c1 c2 c3 ).

  assert (c4 : compose p_prod0 p_prod0 p_term0 (rc0 p_prod0 p_term0 (compose p_prod0 p_prod0 p_term0 
     (id p_prod0)
         Pi_1p0)) (pt_morph0 p_prod0) =  compose p_prod0 p_prod0 p_term0 
          (id p_prod0) Pi_1p0 ).
  rewrite id_unit_right.   compute in  Pi_1Tot0; rewrite Pi_1Tot0.  
  rewrite id_unit_right.   rewrite <- id_unit_left.
  compute in pt_morph_unique_greatest0. 
  apply symmetry. rewrite <- id_unit_right.
  compute in id_is_ptm0; rewrite id_is_ptm0. rewrite <- Pi_1Tot0.  
  compute in pt_morph_unique_greatest0. rewrite <- (pt_morph_unique_greatest0 ). auto.

  assert (c5 : compose p_prod0 p_prod0 x (rc0 p_prod0 x (compose p_prod0 p_prod0 x 
       (id p_prod0) Pi_2p0)) Pi_2p0 =
                        compose p_prod0 p_prod0 x  (id p_prod0)  Pi_2p0 ).
  rewrite id_unit_right.   compute in  Pi_2Tot0; rewrite Pi_2Tot0.   rewrite id_unit_right. auto.

  assert (c6 : compose p_prod0 p_prod0 p_prod0 (rc0 p_prod0 x Pi_2p0) (rc0 p_prod0 p_term0 (pt_morph0 p_prod0)) = rc0 p_prod0 p_prod0 
    (id p_prod0) ).
  compute in  Pi_2Tot0; rewrite Pi_2Tot0. rewrite id_unit_right.  compute in morph_total0; rewrite morph_total0.  
  generalize (IdIsTotal p_prod0) ; compute; intros IdTpr; auto.

  rewrite (pProd_morph_unique0 p_prod0  (pt_morph0 p_prod0) Pi_2p0
                   (id p_prod0) c4 c5 c6 ). auto.

(* id x and map to tX1 *)
  generalize (pProd_morph_rest0 x (pt_morph0 x) (id x) ); compute; intro. compute in pt_morph0.
  compute in pProd_morph_com_4. generalize ( pProd_morph_com_4 x (pt_morph0 x) (id x) ); intro.
  compute in morph_total0. rewrite (morph_total0 x) in H.
  rewrite IdT in H; rewrite id_unit_left in H.
  rewrite <- H0; rewrite id_unit_left .
  compute in rc_d0. rewrite rc_d0.
  compute in Pi_2Tot0;  rewrite Pi_2Tot0. 
  rewrite rc_d0.
  generalize (IdIsTotal p_prod0) ; compute; intros IdTpr; rewrite IdTpr. rewrite id_unit_left; auto.

Defined.


(* lemma shows <f, g> h = <fh, gh> *)
Lemma ProdMapComp `(CRC : CartRestrictionCat ) : forall (a b c d : C), forall (aXb : ParProd a b), 
    forall (f : Hom c a), forall (g : Hom c b), forall (h : Hom d c),
   (pProd_morph_ex c f g) ∘h = pProd_morph_ex d (f ∘h) (g ∘h).
Proof.
  intros.  destruct C; destruct rc0; destruct RC; destruct aXb. compute in pProd_morph_unique0.
  compute. apply (pProd_morph_unique0 d (f ∘ h) (g ∘ h) (compose d c p_prod0 h (pProd_morph_ex0 c f g)));
  compute; compute in pProd_morph_com_3; compute in pProd_morph_com_4.
  rewrite assoc.
  replace (compose d p_prod0 a (compose d c p_prod0 h (pProd_morph_ex0 c f g)) Pi_1p0)
    with (compose _ _ _ h (compose _ _ _ (pProd_morph_ex0 c f g) Pi_1p0)).
  compute in rc8. rewrite <- rc8.
  rewrite <- pProd_morph_com_3. compute in rc7. rewrite rc7. rewrite <- assoc. rewrite <- assoc.
  compute in rc5. rewrite rc5. auto. rewrite assoc. auto.

  rewrite assoc.
  replace (compose d p_prod0 b (compose d c p_prod0 h (pProd_morph_ex0 c f g)) Pi_2p0)
    with (compose _ _ _ h (compose _ _ _ (pProd_morph_ex0 c f g) Pi_2p0)).
  compute in rc8. rewrite <- rc8.
  rewrite <- pProd_morph_com_4. compute in rc7. rewrite rc7. rewrite <- assoc. rewrite <- assoc.
  compute in rc5. rewrite rc5. auto. rewrite assoc. auto.

  compute in pProd_morph_rest0; compute in rc_d0.
  replace (rc0 d p_prod0 (compose d c p_prod0 h (pProd_morph_ex0 c f g))) with 
    (rc0 _ _ (compose _ _ _ h (rc0 _ _ ( pProd_morph_ex0 c f g)))).
  rewrite <- pProd_morph_rest0. compute in rc7. rewrite <- rc7.
  rewrite assoc. compute in rc8. rewrite <- rc8. 
  apply symmetry. rewrite assoc. rewrite <- rc_d0. auto.
  rewrite <- rc_d0. auto.
Defined.


(* lemma shows <f, g> h = <fh, gh> distributivity over total products also *)
Lemma TotProdMapComp `(C : Category ) : forall (a b c d : C), forall (aXb : Product a b), 
    forall (f : Hom c a), forall (g : Hom c b), forall (h : Hom d c),
   (Prod_morph_ex _ _ f g) ∘h = Prod_morph_ex _ _ (f ∘h) (g ∘h).
Proof.
  intros. destruct C; destruct aXb as [aXb]. compute.
  compute in Prod_morph_unique. rewrite (Prod_morph_unique _ 
    (f ∘h) (g ∘h) (compose d c aXb h (Prod_morph_ex c f g))
      (Prod_morph_ex d (compose d c a h f) (compose d c b h g))).
  auto. compute. rewrite <- assoc. rewrite Prod_morph_com_1. auto.
  compute. rewrite <- assoc. rewrite Prod_morph_com_2. auto.
  compute. rewrite Prod_morph_com_1. auto.
  compute. rewrite Prod_morph_com_2. auto.
Defined.



 Record nth_ProdT `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
:=  { npT : Type; npel:> npT; npobj : npT → CRC}.

 Fixpoint nthProdC `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) (n : nat) : nth_ProdT  rc  :=
  match n with
  | O => {| npT := (@ParTerm _ rc CRC); npel := (@RCat_term CRC rc CRC CRC); npobj :=  (@p_term CRC rc CRC )|}
  | S m =>  {| npT := @ParProd _ rc CRC A (npobj rc (nthProdC rc A m) (nthProdC rc A m));
        npel := @RCat_HP CRC rc CRC CRC A (npobj rc (nthProdC rc A m) (nthProdC rc A m));
        npobj := @p_prod CRC rc CRC _ _ |}
end.
    

 Definition nth_Prod_obj `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
    (np : nth_ProdT rc) : CRC := npobj rc np np.
 Coercion nth_Prod_obj : nth_ProdT >-> Obj.

 Fixpoint arrow_to_nthProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC}
(A B : CRC) (f : Hom B A) (n : nat) :
  Hom B (nthProdC rc A n)  :=
  match n with
  | O => @pt_morph CRC rc CRC (@RCat_term CRC rc CRC CRC) B
  | S m => @pProd_morph_ex CRC rc CRC _ _ _ _ f (arrow_to_nthProd rc A B f m)
  end.

(*
(* A^n product in an cartesian restriction category *)
Fixpoint nthProdfix `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat) : RC := 
match n with

  | 0 => RCat_term
  | S 0 => A
  | S m => (RCat_HP A (nthProdfix rc RCat_term RCat_HP A m))

end.



Definition nthProdcoer `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
`(A : Obj) `(n : nat) (B : RC) (pf : B = (nthProdfix rc RCat_term RCat_HP A (S (S n)))) : ParProd A (nthProdfix rc RCat_term RCat_HP A (S n)).
simpl in pf. simpl. generalize dependent pf. intro B. destruct B. elim B.
 exists (RCat_HP A
      match n with
      | 0 => A
      | S _ => RCat_HP A (nthProdfix rc RCat_term RCat_HP A n)
      end). rewrite pf. destruct pf. 
assert ( B

generalize B. rewrite pf in RC. elim pf. exact B.
: forall nthPobj : {nthP : nat*Obj & ((snd nthP) = (nthProdfix rc RCat_term RCat_HP A (fst nthP)) )} ,
ParProd A (nthProdfix rc RCat_term RCat_HP A ((fst (projT1 nthPobj)) - 1)).
intro. destruct nthPobj as [nthP e]. destruct nthP as [n An].
simpl in e. unfold nthProdfix. simpl. unfold nthProdfix in e.
induction n. simpl. rewrite <- e. exact (RCat_HP  A An). 
replace (S n - 1) with n. 

assert (forall m, RCat_HP A (nthProdfix rc RCat_term RCat_HP A m) = (nthProdfix rc RCat_term RCat_HP A (S m))).
 := (nthProdfix rc RCat_term RCat_HP A (S n)).


(* A^n product in an cartesian restriction category *)
Fixpoint nthProdfix `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat) : RC := 
match n with

  | 0 => (RCat_HP A A)
  | S 0 => (RCat_HP A A)
  | S m => (RCat_HP A (nthProdfix rc RCat_term RCat_HP A m))

end.

Fixpoint nProdEq `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat) : Prop :=
match n 

Definition nthProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat)  : (p : ParProd A (nthProdfix rc RCat_term RCat_HP A n)) .

Coercion nthProdfix : Obj >-> ParProd.

(* A^n product in an cartesian restriction category *)
Fixpoint nthProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat) : RC  := 
match n with

  | 0 => RCat_term
  | S 0 => A
  | S m => (RCat_HP A (nthProd rc RCat_term RCat_HP A m))

end.


Definition nthProdC `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) (n : nat) : CRC.
Proof.
  exact (nthProd rc RCat_term RCat_HP A n).
Defined.
*)
(*
Definition nthProdisProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) (n : nat) : ParProd 

Instance nthProdisTerm `{ RC: RestrictionCat  }  : Category := C.

Coercion nthProdisProd : CRC >-> ParProd. *)

Definition prod2TypeN `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) := Hom ( RCat_HP A (nthProdC rc A (S 0))) A .

Definition prod2TypeHP `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC}  (A : CRC) := Hom ( RCat_HP A A) A .

Definition projto_2ndA `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : Obj) (n : nat) : Hom (nthProdC rc A (S n))  A.
Proof. 
  destruct n; unfold nthProdC; simpl. exact (Pi_1p).
   simpl. exact Pi_1p. 
Defined.


Definition proj_twice `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc}  `{CRC : @CartRestrictionCat C rc RC} ( A B D : Obj) : 
Hom (RCat_HP A (RCat_HP B D)) D.
Proof.
  destruct (RCat_HP B D). simpl. destruct (RCat_HP A p_prod0). simpl. exact (Pi_2p0  ∘ Pi_2p1).
Defined.

Definition projto_restAs `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : RC) (n : nat) : Hom (RCat_HP A (nthProdC rc A (S n)))  (nthProdC rc A n).
Proof. 
  simpl. destruct n. simpl. exact (pt_morph _). exact (proj_twice A A  (nthProdC rc A (S n))).
Defined.


(*
Lemma mCoordDecomp `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n m : nat) (f : Hom (nthProdC rc A n) (nthProdC rc A m)) : exists (lf : list (Hom (nthProdC rc A n) A)), 
  (m = length lf) ->  f = (pProd_morph_ex_n A n lf).
*)

Instance CCCsAreCategories `{C : Category} `{ aCCC : @CCC  C}  : Category := C.

Coercion CCCsAreCategories : CCC >-> Category.

(* Define trivial restriction and cartesian restriction categories with the id function as the restriction of every map *)
Definition triv_rc `{C : Category} : rcType C.
Proof.
  unfold rcType. intros. exact (id a).
Defined.

Instance triv_RC `{C : Category} : RestrictionComb C.
Proof.
  exists triv_rc; intros; unfold triv_rc; destruct C; simpl.
  apply id_unit_right. auto.  rewrite id_unit_right. auto.
  rewrite id_unit_right. rewrite id_unit_left. auto. 
Defined.


Instance triv_RCat `{C : Category} : RestrictionCat C triv_RC.
Proof.
  exists .
Defined.

Instance triv_ParTerm `{C : Category} `{T : @Terminal C}  : ParTerm .
Proof.
  destruct T.
 exists terminal t_morph. 
 intros; unfold triv_RC; simpl; unfold triv_rc. auto.
 rewrite <- (t_morph_unique terminal id (t_morph terminal )). auto.
  intros.
 exact (t_morph_unique _ (t_morph b ∘ f) (t_morph a ∘ id)).
Defined.

Check Has_pProducts.

Instance triv_Prods `{C : Category} `{HP : @Has_Products C} : ∀ a b , ParProd a b.
Proof.
  intros.
  destruct (HP a b).
 exists product Pi_1 Pi_2 Prod_morph_ex; intros; unfold triv_RC; simpl; unfold triv_rc.
  auto. auto. rewrite id_unit_right. auto. 
  rewrite Prod_morph_com_1. rewrite id_unit_right. auto.
  rewrite Prod_morph_com_2. rewrite id_unit_right. auto.
  rewrite (Prod_morph_unique _ r1 r2 (pm) ( Prod_morph_ex p' r1 r2)); auto; compute.
  destruct C.
  compute in H. rewrite id_unit_right in H. apply symmetry. auto.
  destruct C.
  compute in H0. rewrite id_unit_right in H0. apply symmetry. auto.
Defined.

(*
Instance triv_Prod_are_prod `{C : Category} :  .
intro HPC. exact (triv_Prods a b). Defined.

Coercion triv_Prods  : Has_Products  >-> Has_pProducts.  _ triv_RC triv_RCat).

Has_Products C ->
*)

(* Coercion triv_RCat_isCat : *)
Instance triv_CRCat (C : Category)  (T : @Terminal C)  (HP : @Has_Products C) : CartRestrictionCat  triv_RC .
Proof.
  exists. exact triv_ParTerm. exact triv_Prods.
Defined.







(* trivial idempotent in CRC - requires extensionality in CRC
Definition idem_triv (C : Category) (rc : @RestrictionComb C) (RC : @RestrictionCat C rc) (CRC :  @CartRestrictionCat C rc RC ) 
  (A : CRC) (e : Hom A A) := forall (f : Hom A A), (((e ∘ f = f) /\ (f = f ∘ e)) -> (f = e)). *)

(* complementary idempotents in CRC - requires unions/extensionality in the CRC 
Definition complement_idem_ext (C : Category) (rc : @RestrictionComb C) (RC : @RestrictionCat C rc) (CRC :  @CartRestrictionCat C rc RC ) 
  (A : CRC) (e e' : Hom A A) := (idem_triv CRC rc CRC CRC A (e ∘ e') ) /\ 
      (forall (b : CRC) (f : Hom b A), (rc _ _ f) = (id b) -> 
          (((rc _ _ (e ∘ p)) = (id ParTerm)) \/ ((rc _ _ e' ∘ p) = (id ParTerm)) ) ). *)







(*

Lemma partial_trm `{C : @Category} `{RC : @RestrictionCat C} `{CRC : @CartRestrictionCat C RC} : 
    ∀ a b, exists (trm_a : Hom a RCat_term) (trm_b : Hom b RCat_term), forall f : Hom a b, (trm_b ∘f = trm_a ∘(rc a b f) 
        /\  (forall (g : Hom a b), (trm_b ∘g = trm_a ∘(rc a b g) -> f = g ) ) ).

  partial_trm : forall a b :  TotR RC, exists (trm_a : Hom a RCat_term) (trm_b : Hom b RCat_term), forall f : Hom a b, (trm_b ∘f = trm_a ∘(rc a b f) 
          /\  (forall (g : Hom a b), (trm_b ∘g = trm_a ∘(rc a b g) -> f = g ) ) )  


Lemma partial_trm `{RC : RestrictionCat } : 
    forall (a b : Tot RC), forall (f : Hom a b), id a = rc f.

forall RCat_term : Terminal (Tot RC), 
        exists (trm_a : Hom a RCat_term) (trm_b : Hom b RCat_term), forall f : Hom a b, (trm_b ∘f = trm_a ∘(rc a b f) 
        /\  (forall (g : Hom a b), (trm_b ∘g = trm_a ∘(rc a b g) -> f = g ) ) ).

*)

(*

Lemma partial_prod `{CRC : CartRestrictionCat} :

*)

(*
(* Cartesian Closed Category : one that has terminal element, binary products (all finite products) and exponential *)
Class CCC (C : Category) : Type :=
{
  CCC_term : Terminal C;
  CCC_HP : Has_Products C;
  CCC_HEXP : Has_Exponentials C
}.

Arguments CCC_term _ {_}, {_ _}.
Arguments CCC_HP _ {_} _ _, {_ _} _ _.
Arguments CCC_HEXP _ {_} _ _, {_ _} _ _.

Existing Instances CCC_term CCC_HP CCC_HEXP.


  }.

*)