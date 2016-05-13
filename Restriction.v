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

(* Type of a restriction combinator *)
Definition rcType (C : Category): Type.
Proof.
  exact (forall a b : C, Hom a b -> Hom a a ).
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

(* Definition Has_RestrictionComb (C : Category) :=  RestrictionComb C. *)

Coercion rc : RestrictionComb >-> rcType.

(* proof of rc_d from rc1...rc4 rules *)
Lemma rc_d_pf : forall (C : Category), forall RC : RestrictionComb C, forall (a b c: Obj), forall (f : Hom a b), forall (g : Hom b c), rc a c (compose f g) = rc a b (compose f (rc b c g) ).
Proof.
Admitted. 



(* Restriction category *)
Class RestrictionCat (C : Category)  (rc : RestrictionComb C) : Type :=
{
  RCat_RC : RestrictionComb C := rc
  ; rc_d := rc_d_pf C RCat_RC
}.

Instance RestrictionCatsAreCategories `{ RC: RestrictionCat  }  : Category := C.

Coercion RestrictionCatsAreCategories : RestrictionCat >-> Category.

(* id is a total map *)
Definition IdIsTotal `{RC : RestrictionCat} : ∀ a : C, rc _ _ (id a) = id a.
Proof.
  intro; destruct C;  destruct RC; destruct rc0; compute.
  rewrite <- (id_unit_left a a (rc0 a a (id a))).
  compute in rc5.
  rewrite (rc5 a a (id a)).
  reflexivity.
Defined.

(* X is a retract of Y when *)
Definition isRetractOf `{C : Category} : Obj -> Obj -> Prop.
Proof.
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
Proof.
  destruct RC.
  destruct rc.
  intros a b f.
  exact (rc0 a b f = id a).
Defined.


(* A subcategory of a restriction category with the same objects as the restriction category and only the total maps *)
Definition Tot `{C : Category} `(rc : @RestrictionComb C) : RestrictionCat C rc -> Category.
Proof.
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
Proof.
  destruct C; destruct RC; destruct RCat_RC0.
  exact (g ∘(rc a b f) = f).
Defined.


(* consider total subcategory object a as an object of to full restriction category *)
Definition fc `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} (a : TotR rc RC) : RC.
Proof.
  destruct C; destruct RC; destruct a.
  compute in x.
  compute.
  exact x.
Defined.

(* consider total subcategory object a as an object of to full restriction category *)
Definition sc `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} (a : RC) : TotR rc RC.
Proof.
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

(* define total projection maps in a total subcategory of a cartesian restriciton category *)
Definition Pi_1map `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), Hom (sc rc aXPb) a.
Proof.
  destruct (TotR rc RC).
  destruct aXPb as [aXPb]. 
  destruct C; destruct RC. destruct rc.
  compute in Pi_1p0. compute.
  exists Pi_1p0. exact Pi_1Tot0.
Defined.

Definition Pi_2map `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), Hom (sc rc aXPb) b.
Proof.
  destruct (TotR rc RC).
  destruct aXPb as [aXPb]. 
  destruct C; destruct RC. destruct rc.
  compute in Pi_2p0. compute.
  exists Pi_2p0. exact Pi_2Tot0.
Defined.


(* define total unique product map in a total subcategory of a cartesian retriction category *)
Definition Prod_morphs `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), (∀ (p : TotR rc RC) (r1 : Hom p a) (r2 : Hom p b), Hom p (sc rc aXPb)).
Proof.
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


(* a partial product in a restriction category is a total product in its total subcategory *)
Lemma pp_isProdInTot `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), exists (aXb : Product a b), sc rc aXPb = aXb.
Proof.
  intros. 
  assert (aXb : Product a b).

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

  assert (sigeq : forall (v w : {f0 : Hom p b | rc0 p b f0 = id p}), v = w -> proj1_sig v = proj1_sig w).
  intros. rewrite H. auto. 
  intros. compute in f; compute in g. destruct f as [f]; destruct g as [g].
  compute in H; compute in H0; compute in H1; compute in H2.
  assert (Hp1 : (compose p aXPb a f Pi_1p0) = r1).
  rewrite sigeq.
  assert (fg : f = g). 
  compute in pProd_morph_unique0. generalize ( pProd_morph_unique0 p r1 r2 f).
  assert (au1 : (compose p p a (rc0 p a (compose p aXPb a f Pi_1p0)) r1 = compose p aXPb a f Pi_1p0)).
  rewrite H.
  compute in H. generalize H. compute in t. rewrite (pf_ir (rc0 p aXPb f = id p) e t).
  apply H.
  


(* a partial product in a restriction category is a total product in its total subcategory *)
Lemma pp_isProdInTot `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : forall (a b : TotR rc RC), 
   forall (aXPb : ParProd (fc rc a) (fc rc b)), exists (aXb Product a b), sc rc aXPb = aXb.


(* Define a partial product based on total product definition *)
Definition ParP `{RC : RestrictionCat } (a b : TotR RC) (aXb : Product a b) : ParPClass a b aXb.
Proof.
  exists; destruct C; destruct RC; compute.
  exact (fullCatObj aXb).
  destruct a as [a a1]; destruct b as [b b1]; destruct aXb.
  destruct RCat_RC0.
  compute in Pi_1; destruct Pi_1 as [p1 p1t].
  exact p1.
  destruct a as [a a1]; destruct b as [b b1]; destruct aXb.
  destruct RCat_RC0.
  compute in Pi_2; destruct Pi_2 as [p2 p2t].
  exact p2.
  intros.
  destruct a as [a a1]; destruct b as [b b1]; destruct aXb.
  destruct RCat_RC0.
  compute in Prod_morph_ex.
  generalize (Prod_morph_ex ( (exist (fun (t : Obj) => True) p' ) I)).
  intros.
  assert (p'' : {_ : Obj | True}).
  exact ( (exist (fun (t : Obj) => True) p' ) I).

Defined.
*)


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


(* a restriction category with a restriction terminal object and restriction products is a Cartesian restriction category *)
Class CartRestrictionCat `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc}  : Type :=
{
  RCat_term : ParTerm ;
  RCat_HP : Has_pProducts 
}.


Instance CartRestrictionCatsAreCategories `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) `(CRC : @CartRestrictionCat C rc RC)  : RestrictionCat C rc := RC.

Coercion CartRestrictionCatsAreCategories : CartRestrictionCat >-> RestrictionCat.


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
(*  destruct (pProd_morph_unique0 p_prod0 Pi_1p0 (pt_morph0 p_prod0)
                     (compose p_prod0 x p_prod0 Pi_1p0 (pProd_morph_ex0 x (id x) (pt_morph0 x)))  ).
*)
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


(* a map f : Z x X -> Y admits a T_{x,y} index when *)
Definition fAdmitsTxy `{CRC : CartRestrictionCat} (a x y : RC) (aXx : ParProd a x) (Txy : Hom aXx y) : 
   forall z : RC, forall zXx : ParProd z x, (Hom  zXx y) -> Prop.
Proof.
  intros z zXx f.
  exact (exists (h : Hom z a), (TotMaps _ _ _ _ h) /\ (f = Txy ∘(pProd_morph_ex zXx (h ∘Pi_1p) Pi_2p))).
Defined.

(* a T_{x,y} index is universal when *)
Definition TxyUniv `{CRC : CartRestrictionCat} (a x y : RC) (aXx : ParProd a x) (Txy : Hom aXx y) : Prop .
Proof.
  exact (forall z : RC, forall zXx : ParProd z x, forall (f : Hom zXx y), fAdmitsTxy a x y aXx Txy z zXx f).
Defined.

(* A is a Turing object when *)
Definition TuringObj `{CRC : CartRestrictionCat} (a : RC) : Prop := 
  forall x y, forall (aXx : ParProd a x), exists (Txy : Hom aXx y), TxyUniv a x y aXx Txy.

(* a Cartesian restriction category with a Turing object is a Turing category *)
(* Application bullet has to be given explicitly, non-constructive otherwise *)
Class TuringCat `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC}  (A : Obj) : Type :=
{
  AisTuring : TuringObj A 
(*  bullet : Hom (RCat_HP A A) A ;
  bulletUniv : TxyUniv A A A (RCat_HP A A) bullet  *)
}.



(* every object in a Turing category is a retract of a Turing object *)
Lemma everyObjisRetract `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
  `(A : Obj) `{T : @TuringCat C rc RC CRC A} : forall x : C, isRetractOf x A.
Proof.
  intros.
  unfold isRetractOf.
  generalize (xX1and1XxIsox CRC); intro xX1and1XxIsox.
  generalize (ProdMapComp CRC); intro ProdMapComp.
  destruct T; destruct C; destruct RC; destruct CRC;  destruct rc.
  generalize (IdIsTotal x) ; compute; intros IdT.
  compute in AisTuring0; compute in x; compute in A;  compute in rc0.
  compute in xX1and1XxIsox.
  generalize (xX1and1XxIsox x RCat_term0).
  destruct RCat_term0. 
  generalize (ProdMapComp A p_term0 A x (RCat_HP0 A p_term0)); intro ProdMapCompA1.  
  generalize (ProdMapComp A p_term0 (RCat_HP0 x p_term0) x (RCat_HP0 A p_term0)); intro ProdMapCompA2.  
  compute in ProdMapCompA1; compute in ProdMapCompA2.
  intro xX1Isox.
  compute in p_term0; compute in pt_morph0; compute in RCat_HP0.

  generalize (AisTuring0 p_term0 x (RCat_HP0 A p_term0)); destruct (RCat_HP0 A p_term0) as [AX1]; intro THyp. 

  destruct THyp as [Tmap THyp1] . 
  generalize (THyp1 x (RCat_HP0 x p_term0)).

  compute in xX1Isox; destruct xX1Isox as [iso1 iso2].
  generalize (iso1  (RCat_HP0 x p_term0)) .

  destruct (RCat_HP0 x p_term0) as [xX1]; intros [iso11 iso12] THyp.
  destruct (THyp Pi_1p1) as [PiTxX1 H]; destruct H.
  exists PiTxX1.
  exists ( Tmap ∘(pProd_morph_ex0 A (id A) (pt_morph0 A))).
  compute; rewrite assoc.
  assert (temp : id x = compose _ _ _ (pProd_morph_ex1 x (id x) (pt_morph0 x))  (compose xX1 AX1 x (pProd_morph_ex0 xX1 (compose xX1 x A Pi_1p1 PiTxX1) Pi_2p1) Tmap)  ).
  rewrite <- H0; exact iso12.
  rewrite assoc in temp.
  rewrite ProdMapCompA1. rewrite id_unit_left. compute in pt_morph_unique_greatest0. rewrite (pt_morph_unique_greatest0).
  rewrite H. rewrite id_unit_right.
  rewrite ProdMapCompA2 in temp.
  compute in pProd_morph_com_6. rewrite <- pProd_morph_com_6 in temp.
  compute in rc_d0; rewrite rc_d0 in temp.
  compute in Pi_2Tot1; rewrite Pi_2Tot1 in temp. rewrite id_unit_left in temp.
  compute in pProd_morph_rest1; rewrite <- pProd_morph_rest1 in temp.
  rewrite IdT in temp. rewrite id_unit_left in temp. 
  compute in rc5; rewrite rc5 in temp.
  rewrite assoc in temp.
  rewrite temp.
  compute in pProd_morph_com_5; rewrite <- pProd_morph_com_5.
  rewrite rc_d0. compute in Pi_1Tot1; rewrite Pi_1Tot1.
  rewrite id_unit_left . rewrite id_unit_left .
  rewrite <- pProd_morph_rest1.
  rewrite IdT; compute in morph_total0; rewrite morph_total0.
  rewrite id_unit_left . rewrite id_unit_right; auto.
Defined.


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

Definition prod2TypeN `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) := Hom ( RCat_HP A (nthProdC rc A (S 0))) A .

Definition prod2TypeHP `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC}  (A : CRC) := Hom ( RCat_HP A A) A .

Definition projto_2ndA `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : Obj) (n : nat) : Hom (nthProdC rc A (S n))  A.
Proof. 
  destruct n; unfold nthProdC; simpl. exact (id A).
   simpl. exact Pi_1p. 
Defined.


Definition proj_twice `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc}  `{CRC : @CartRestrictionCat C rc RC} ( A B D : Obj) : 
Hom (RCat_HP A (RCat_HP B D)) D.
Proof.
  destruct (RCat_HP B D). simpl. destruct (RCat_HP A p_prod0). simpl. exact (Pi_2p0  ∘ Pi_2p1).
Defined.

Definition projto_restAs `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : RC) (n : nat) : Hom (RCat_HP A (nthProd rc RCat_term RCat_HP A (S n)))  (nthProd rc RCat_term RCat_HP A n).
Proof. 
  simpl. destruct n. simpl. exact (pt_morph (RCat_HP A A)). exact (proj_twice A A  (nthProdC rc A (S n))).
Defined.

Definition bulletn_once `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : RC) (n : nat) (bullet : Hom (RCat_HP A A) A) : 
Hom ( RCat_HP A (nthProdC rc A (S n))) ( RCat_HP A (nthProdC rc A n)) .
Proof.
  assert (p1 : Hom (RCat_HP A (nthProdC rc A (S n))) A).
  destruct  (RCat_HP A (nthProdC rc A (S n))). exact (Pi_1p0).
  exact (pProd_morph_ex (RCat_HP A (nthProdC rc A (S n))) (bullet  ∘(pProd_morph_ex (RCat_HP A (nthProdC rc A (S n))) 
    p1 ((projto_2ndA A n) ∘Pi_2p) ))
  (projto_restAs A n)).
Defined.


(* n-fold application of bullet *)
Fixpoint bullet_n `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n : nat) (bullet : Hom (RCat_HP A A) A) : Hom ( RCat_HP A (nthProd rc RCat_term RCat_HP A n)) A  := 
match n with
  | 0 => bullet ∘(pProd_morph_ex A (id A) (id A)) ∘Pi_1p
  | S m => (bullet_n A m bullet ) ∘(bulletn_once  A m bullet)
end.

Open Scope list_scope.

(* n-fold product of maps A^n -> A *)
Fixpoint pProd_morph_ex_n `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n : nat) (lf : list (Hom (nthProdC rc A n) A)) : Hom (nthProdC rc A n) (nthProdC rc A (length lf))  := 
match lf with
  | nil => pt_morph (nthProdC rc A n)    
  | f :: nil => f
  | f :: lf' => (pProd_morph_ex (nthProdC rc A n) f (pProd_morph_ex_n A n lf' ))
end.

(*
Lemma mCoordDecomp `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n m : nat) (f : Hom (nthProdC rc A n) (nthProdC rc A m)) : exists (lf : list (Hom (nthProdC rc A n) A)), 
  (m = length lf) ->  f = (pProd_morph_ex_n A n lf).
*)

(* What it means for f : A^n -> A to be an computable *)
Definition f_comp `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) (n : nat) (f : Hom (nthProdC rc A n) A) : Prop := 
  exists (p : Hom RCat_term A), f = (bullet_n A n bullet) ∘(pProd_morph_ex (nthProdC rc A n) 
    (p ∘(pt_morph (nthProdC rc A n))) (id (nthProdC rc A n))).

(* What it means for (A, bullet) to be an applicative structure, shown for each n *)
Fixpoint isAppStructForn `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  (n : nat) (lf : list (Hom (nthProdC rc A n) A))  : Prop :=
match lf with
  | nil => True
  | f :: lf' => (f_comp A bullet n f) /\ (isAppStructForn A bullet n lf' )
end.

(* What it means for (A, bullet) to be an applicative structure *)
Definition isAppStruct `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) : Prop :=
forall (n : nat), forall (lf : list (Hom (nthProdC rc A n) A)), isAppStructForn A bullet n lf.

(*
Variable C : Category.
Variable aCCC : CCC C.
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

Instance triv_ParTerm `{C : Category} `{T : @Terminal C}  : ParTerm .
Proof.
  destruct T.
 exists terminal t_morph. 
 intros; unfold triv_RC; simpl; unfold triv_rc. auto.
 rewrite <- (t_morph_unique terminal id (t_morph terminal )). auto.
  intros.
 exact (t_morph_unique _ (t_morph b ∘ f) (t_morph a ∘ id)).
Defined.

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
  simpl in Prod_morph_com_1; simpl in Prod_morph_com_2.
 (* rewrite (Prod_morph_com_1.
  simpl in H; simpl in H0
 
  compute. *)
Admitted.


Instance triv_RCat `{C : Category} : RestrictionCat C triv_RC.
Proof.
  exists .
Defined.

(* Coercion triv_RCat_isCat : *)

Instance triv_CRCat (C : Category)  (T : @Terminal C)  (HP : @Has_Products C) : CartRestrictionCat  triv_RC .
Proof.
  exists. exact triv_ParTerm. exact triv_Prods.
Defined.

(* Coercion triv_CRCat_isRCat : *)

Definition TuringObjIn (C : Category) (rc : @RestrictionComb C) (RC : @RestrictionCat C rc) (CRC :  @CartRestrictionCat C rc RC )(a : CRC) : Prop := TuringObj a.

(*
Instance CCCsAreCategories `{C : Category} `{ aCCC : @CCC  C}  : Category := exponential.

Coercion ExpIsObj : Exponential >-> C. *)


Theorem aTuringCCC `{C : Category} `{aCCC : @CCC C} : forall A : (triv_CRCat aCCC CCC_term CCC_HP), (forall b : (triv_CRCat aCCC CCC_term CCC_HP), isRetractOf b A ) 
-> TuringObjIn C triv_RC (triv_RCat ) (triv_CRCat aCCC CCC_term CCC_HP) A.
Proof.
  intro.  intros retractH. unfold TuringObjIn. unfold TuringObj. intros.
  destruct (triv_CRCat aCCC CCC_term CCC_HP). destruct triv_RCat. destruct (triv_RC ) .
  destruct C. destruct aCCC. compute in CCC_HP; compute in CCC_HEXP.
  destruct (CCC_HP (CCC_HEXP A A) A) as [AtoAxA]. destruct (CCC_HP AtoA A).
simpl in eval.
  compute in aXx.  
  destruct aXx as [aXx]. compute.
  destruct (retractH y) as [my]. destruct H as [ry].
  destruct (retractH x) as [mx]. destruct H0 as [rx].
  destruct (CCC_HP AtoA A) as [AtoAxA].
  compute in RCat_HP0. compute in AtoAxA.
  destruct (retractH AtoA) as [mAtoA].
  destruct H1 as [rAtoA]. simpl in eval.
  destruct (CCC_HP AtoA A) as [AtAxA].

  exists (ry ∘eval ∘(Prod_morph_ex aXx ( rAtoA ∘Pi_1p0 ) (mx ∘Pi_2p0 ) )).


  generalize  eval. compute. intro. Check eval.
 intro. simpl in eval.
  destruct (CCC_HP AtoA A).
  compute in A.
  destruct triv_RCat. 



Theorem aTuringCCC : (exists A : aCCC, (forall b : aCCC, isRetractOf b A) -> exists A : aCCC, TuringObj A.
Proof.
  intros. destruct H as [A]. exists A. 
  unfold TuringObj. intros. destruct aCCC.
 (* destruct aXx as [aXx]. *)
  unfold TxyUniv.
  destruct (H y). destruct H0.
  unfold fAdmitsTxy. simpl. 
  destruct (H x); destruct H1. unfold triv_rc. 
(*  destruct (CCC_HP (CCC_HEXP A A) A) as [AtoAxA]. *)

  destruct (CCC_HP A A) as [AxA p1 p2 pm].
  
  destruct (H (CCC_HEXP A A)). destruct H2.

  destruct (CCC_HEXP A A).
  simpl in eval.
  destruct (CCC_HP e A) as [AtoAxA].

Check ( (Prod_morph_ex aXx AxA ( Pi_1p ) (x2 ∘Pi_2p ) )).
  exists (x1 ∘eval ∘(Prod_morph_ex aXx ( x3 ∘Pi_1p0 ) (x4 ∘Pi_2p0 ) )).

(CCC_HP A x)
  compute in eval.
  destruct aCCC.

  generalize eval.
  Check eval.
  destruct (CCC_HP AtoA A) as [AtoAxA].
  destruct (let
        (Obj, Hom, compose, _, _, id, _, _) as Category return (Category → Category → Type) := C in
        Hom)
         (let
          (product, Pi_1, Pi_2, Prod_morph_ex, _, _, _) :=
          (let (_, CCC_HP, _) := aCCC in CCC_HP) AtoA A in
          product)).
  Check product.
  generalize eval.
  destruct C.

 intro.


Definition Comp `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) : TuringCat rc A.
exists . unfold TuringObj. intros. exists 

Instance 

 :=
forall (n : nat), forall (lf : list (Hom (nthProdC rc A n) A)), isAppStructForn A bullet n lf.


Lemma equivDef `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) (bullet : Hom (RCat_HP A A) A) : ((forall X : CRC, isRetractOf X A) /\ (isAppStruct A bullet))
   -> TuringCat rc A.
Proof.
  intro. destruct H. destruct CRC. destruct RC. destruct rc. unfold isAppStruct in H0. unfold isAppStructForn in H0.
  unfold f_comp in H0. destruct RCat_term0. destruct (RCat_HP0 A A) as [AXA]. 
 
  assert (bullet' : Hom AXA A).
  exists.
  unfold TuringCat. simpl. unfold TxyUniv. unfold fAdmitsTxy. simpl. intros. unfold isRetractOf in H. 
  unfold f_comp in H0. destruct RCat_term0. destruct (RCat_HP0 A A) as [AXA]. 
  assert (Txy_1 : Hom A A). destruct C. simpl in H. elim (H (AXA)).
   ∘(pProd_morph_ex0 A g (pt_morph0 A))

generalize (H0 (S 0)). 
  assert (ff : (Hom (nthProdC {| rc := rc0; rc1 := rc5; rc2 := rc6; rc3 := rc7; rc4 := rc8 |} A 1) A)). compute. destruct C.
  
compute. intro. in H0
  destruct bullet.
 destruct (H0   
r_y ∘(pProd_morph_ex AXA (Txy_1 ∘Pi_1p) Pi_2p) ∘(pProd_morph_ex aXx Pi_1p m_x)

destruct RCat_HP0. compute in x; compute in y.
simpl in H0.
 exists.

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