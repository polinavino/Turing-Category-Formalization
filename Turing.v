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

Require Import Main_Category.
Require Import CCC.
Require Import Coq.Setoids.Setoid.
Require Import Restriction.
Require Import PCA.
Require Import Coq.Lists.List.
Require Import CompA.
Require Import Main_Func.

Generalizable All Variables. 


(* a map f : Z x X -> Y admits a T_{x,y} index when *)
Definition fAdmitsTxy `{CRC : CartRestrictionCat} (a x y : RC) (aXx : ParProd a x) (Txy : Hom aXx y) : 
   forall z : RC, forall zXx : ParProd z x, (Hom  zXx y) -> Prop.
  intros z zXx f.
  exact (exists (h : Hom z a), (TotMaps _ _ _ _ h) /\ (f = Txy ∘(pProd_morph_ex zXx (h ∘Pi_1p) Pi_2p))).
Defined.

(* a T_{x,y} index is universal when *)
Definition TxyUniv `{CRC : CartRestrictionCat} (a x y : RC) (aXx : ParProd a x) (Txy : Hom aXx y) : Prop .
  exact (forall z : RC, forall zXx : ParProd z x, forall (f : Hom zXx y), fAdmitsTxy a x y aXx Txy z zXx f).
Defined.

(* A is a Turing object when *)
Definition TuringObj `{CRC : CartRestrictionCat} (A : RC) : Prop := 
  forall x y, forall (aXx : ParProd A x), exists (Txy : Hom aXx y), TxyUniv A x y aXx Txy.

(* 
(* bullet is an applicative map when *)
Definition TuringMorph `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) `(A : CRC) `( T : @TuringCat C rc RC CRC A ) 
  (AxA : ParProd A A) (bullet : Hom AxA A) : Prop := TxyUniv A A A AxA bullet.
 *)


(* a Cartesian restriction category with a Turing object is a Turing category *)
Class TuringCat `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC}  (A : Obj) : Type :=
{
  AisTuring : TuringObj A 
}.


(* bullet is an applicative map when *)
Definition TuringMorph `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) `(A : CRC) `( T : @TuringCat C rc RC CRC A ) 
  (bullet : Hom (RCat_HP A A) A) : Prop := TxyUniv A A A (RCat_HP A A) bullet.

(* bullet is an applicative map when *)
Definition CompMorph `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) `(A : CRC) 
  (bullet : Hom (RCat_HP A A) A) : Prop :=
  forall (f : Hom  (RCat_HP A A) A), exists (h : Hom A A), 
  (TotMaps _ _ _ _ h) /\ (f = bullet ∘(pProd_morph_ex (RCat_HP A A) (h ∘Pi_1p) Pi_2p)).

(* define coercion *)
Instance TuringCatsAreCartRestCategories `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) `(A : CRC) `{ T : @TuringCat C rc RC CRC A }
  : CartRestrictionCat rc := CRC.

Coercion TuringCatsAreCartRestCategories : TuringCat >-> CartRestrictionCat.


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
  compute in AisTuring0; compute in x; compute in A;  compute in rc.
  compute in xX1and1XxIsox.
  generalize (xX1and1XxIsox x RCat_term).
  destruct RCat_term. 
  generalize (ProdMapComp A p_term A x (RCat_HP A p_term)); intro ProdMapCompA1.  
  generalize (ProdMapComp A p_term (RCat_HP x p_term) x (RCat_HP A p_term)); intro ProdMapCompA2.  
  compute in ProdMapCompA1; compute in ProdMapCompA2.
  intro xX1Isox.
  compute in p_term; compute in pt_morph; compute in RCat_HP.

  generalize (AisTuring0 p_term x (RCat_HP A p_term)); destruct (RCat_HP A p_term) as [AX1]; intro THyp. 

  destruct THyp as [Tmap THyp1] . 
  generalize (THyp1 x (RCat_HP x p_term)).

  compute in xX1Isox; destruct xX1Isox as [iso1 iso2].
  generalize (iso1  (RCat_HP x p_term)) .

  destruct (RCat_HP x p_term) as [xX1]; intros [iso11 iso12] THyp.
  destruct (THyp Pi_1p0) as [PiTxX1 H]; destruct H.
  exists PiTxX1.
  exists ( Tmap ∘(pProd_morph_ex A (id A) (pt_morph A))).
  compute; rewrite assoc.
  assert (temp : id x = compose _ _ _ (pProd_morph_ex0 x (id x) (pt_morph x))  (compose xX1 AX1 x (pProd_morph_ex xX1 (compose xX1 x A Pi_1p0 PiTxX1) Pi_2p0) Tmap)  ).
  rewrite <- H0; exact iso12.
  rewrite assoc in temp.
  rewrite ProdMapCompA1. rewrite id_unit_left. compute in pt_morph_unique_greatest. rewrite (pt_morph_unique_greatest).
  rewrite H. rewrite id_unit_right.
  rewrite ProdMapCompA2 in temp.
  compute in pProd_morph_com_3. rewrite <- pProd_morph_com_3 in temp.
  compute in rc_d; rewrite rc_d in temp.
  compute in Pi_2Tot0; rewrite Pi_2Tot0 in temp. rewrite id_unit_left in temp.
  compute in pProd_morph_rest0; rewrite <- pProd_morph_rest0 in temp.
  rewrite IdT in temp. rewrite id_unit_left in temp. 
  compute in rc1; rewrite rc1 in temp.
  rewrite assoc in temp.
  rewrite temp.
  compute in pProd_morph_com_0; rewrite <- pProd_morph_com_0.
  rewrite rc_d. compute in Pi_1Tot0; rewrite Pi_1Tot0.
  rewrite id_unit_left . rewrite id_unit_left .
  rewrite <- pProd_morph_rest0.
  rewrite IdT; compute in morph_total; rewrite morph_total.
  rewrite id_unit_left . rewrite id_unit_right; auto.
Defined.



(* If a CCC contains an object of which every other object is a retract, it is a Turing category with trivial restriction structure *) 
Theorem aTuringCCC `{C : Category} `{aCCC : @CCC C} : 
  forall A : (triv_CRCat aCCC CCC_term CCC_HP), ((forall b : (triv_CRCat aCCC CCC_term CCC_HP), isRetractOf b A )   
  -> @TuringObj C triv_RC (triv_RCat ) (triv_CRCat aCCC CCC_term CCC_HP) A).
Proof.
  intro.  intros retractH. unfold TuringObj. unfold TuringObj. intros.
  generalize (fun Y Z => ProdMapComp _ A x Y Z aXx). intro pmcAX. 
  generalize (fun Y Z => TotProdMapComp C (CCC_HEXP A A) A Y Z (CCC_HP (CCC_HEXP A A) A) ). compute in pmcAX.
  intro tpmcAAtoA. compute in tpmcAAtoA.
  generalize (ProdMapComp _ ). intro pmcTRC. compute in pmcTRC.
  destruct (triv_CRCat aCCC CCC_term CCC_HP) .
  destruct triv_RCat. 
  unfold triv_RC in RCat_RC. unfold triv_rc in RCat_RC.

  destruct C. destruct aCCC. compute in CCC_HP; compute in CCC_HEXP. compute in RCat_RC.
  unfold rc in RCat_RC. compute in RCat_RC. 
  destruct (CCC_HEXP A A) as [AtoA]. compute in AtoA.  

  simpl in eval. simpl in Exp_morph_ex. simpl in Exp_morph_com. simpl in Exp_morph_unique.
  destruct (CCC_HP AtoA A) as [AtoAxA]. 
  compute in aXx.  
  destruct (retractH y) as [my]. destruct H as [ry].
  destruct (retractH x) as [mx]. destruct H0 as [rx].
  compute in RCat_HP. compute in AtoAxA.
  destruct (retractH AtoA) as [mAtoA].
  destruct H1 as [rAtoA].
  exists (ry ∘eval ∘(Prod_morph_ex aXx ( rAtoA ∘Pi_1p ) (mx ∘Pi_2p ) )).
  
  unfold TxyUniv. intros. unfold fAdmitsTxy. compute in f. compute. 
  generalize dependent (Exp_morph_com z).   generalize dependent (Exp_morph_ex z).
  destruct (CCC_HP z A) as [zXA]. compute. intro pmex. intro pmc.  
  generalize (fun Y W => pmcTRC z x Y W zXx). intro pmcAZ. compute in pmcAZ.
  destruct zXx as [zXx].
  exists (compose z AtoA A (pmex (compose _ _ _ (pProd_morph_ex _ Pi_0 (rx ∘Pi_3) ) (compose _ _ _ f my))) mAtoA).

  destruct aXx as [AXx]. split; compute. auto. (* Check Pi_3 zXA. Check Pi_2p zXx. Check Pi_2p0 AXx. *)
  rewrite assoc. rewrite assoc.
  rewrite id_unit_left in pmc. 
  rewrite tpmcAAtoA. rewrite assoc. 
  compute in pProd_morph_com_0. rewrite <- pProd_morph_com_0.
  rewrite id_unit_right. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
  compute in H1. rewrite H1. rewrite id_unit_left.
  rewrite assoc. rewrite assoc. rewrite assoc.
  compute in pProd_morph_com_3. rewrite <- pProd_morph_com_3. 
  rewrite id_unit_right. 
  replace Pi_1p with (compose _ _ _ (Prod_morph_ex0 _ (Pi_1p) (compose _ _ _ Pi_2p  mx)) Pi_0).
  replace (Prod_morph_ex0 zXx Pi_1p (compose zXx x A Pi_2p mx)) with
    (Prod_morph_ex0 zXx Pi_1p (compose zXx x A (compose _ _ _ (id _) Pi_2p) mx)).
  replace (compose zXx x A Pi_2p mx) with
    (compose zXx zXA A (Prod_morph_ex0 _ (Pi_1p) (compose _ _ _ Pi_2p  mx)) Pi_3).
  rewrite id_unit_right. rewrite <- assoc. rewrite <- assoc.
  rewrite <- (tpmcAAtoA zXA zXx). rewrite assoc. 
  rewrite <- (assoc _ _ _ _ _ _ eval). compute. 
  rewrite <- (pmc ((compose zXA y A
                 (compose zXA zXx y (pProd_morph_ex zXA Pi_0 (compose zXA A x Pi_3 rx)) f) my))).
  rewrite <- assoc. rewrite <- assoc. compute in H. rewrite H.
  rewrite id_unit_left. rewrite assoc. rewrite pmcAZ.
  rewrite Prod_morph_com_0. rewrite assoc. rewrite Prod_morph_com_3.
  rewrite <- assoc. compute in H0. rewrite H0. rewrite id_unit_left.
  replace (pProd_morph_ex zXx Pi_1p Pi_2p) with (id zXx).
  rewrite id_unit_right. auto.
  apply pProd_morph_unique. compute. auto. compute. auto.
  compute. rewrite id_unit_right. auto.
  compute in Prod_morph_com_3. rewrite Prod_morph_com_3. auto.
  rewrite (id_unit_right zXx). auto.
  compute in Prod_morph_com_0. rewrite Prod_morph_com_0. auto.
Defined.
  

(* an object in a category with Turing object A is Turing if and only if it is a retract of A *)
Lemma ARetOfeveryTO `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
  `(A : Obj) `{T : @TuringCat C rc RC CRC A} : forall A' : C, @TuringObj T rc T T A' <-> isRetractOf A A'.
Proof. 
  intros. split. intro. assert (T' : TuringCat rc A'). exists. apply H.
  apply (everyObjisRetract rc A' A).
  intro. unfold TuringObj. unfold TuringObj. unfold TxyUniv. unfold fAdmitsTxy.
  generalize (@everyObjisRetract T rc T T A T). intro everyOR.
  generalize (@mIsTotal T rc T). intro mIsTotal. intros x y aXx'. 
  assert (pmc : forall (a b : C), forall (aXb : ParProd a b), forall (c d : C),
    forall (f : Hom c a), forall (g : Hom c b), forall (h : Hom d c),
   (pProd_morph_ex c f g) ∘h = pProd_morph_ex d (f ∘h) (g ∘h)). intros.
  exact (@ProdMapComp T rc T T a b c d aXb f g h).
  destruct T. unfold TuringObj in AisTuring0. 
  destruct CRC. 
  generalize (RCat_HP A x). intro Axx.
  generalize (pmc A x Axx aXx'). intro pmcaxax'.
  destruct (AisTuring0 x y Axx).
  destruct RC; destruct C; destruct rc.  
  unfold TxyUniv in H0. destruct H as [m]. destruct H as [r].
  exists (x0 ∘ pProd_morph_ex _ (r ∘ Pi_1p) (Pi_2p )).
  generalize (pmc A' x aXx' Axx). intro pmcapxax.
  intros z zXx f. 
  destruct (H0 z zXx f) as [h]. destruct H1.
  generalize (pmc A x Axx zXx). intro pmczxax.
  destruct Axx as [Axx]. compute. compute in H2. 
  destruct aXx' as [aXx']. compute in pmcapxax; compute in pmcaxax'. 
  destruct zXx as [zXx]. compute in everyOR. destruct (everyOR z) as [mz]. destruct H3 as [rz].
  compute in f.
  exists (compose _ _ _ h m). split. rewrite rc_d. compute.  
  generalize (mIsTotal A A' m r H). compute. intro mT.
  generalize (mIsTotal z A mz rz H3). compute. intro zmT.
  rewrite mT. rewrite id_unit_left. compute in H1. exact H1.
  compute. rewrite assoc. rewrite pmcaxax'. compute in pmczxax.
  compute in x0. rewrite assoc.
  replace (compose zXx aXx' A'
           (pProd_morph_ex0 zXx (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1) Pi_1p0) with
      (compose zXx z A' Pi_1p1 (compose z A A' h m)).
  replace  (compose zXx aXx' x 
        (pProd_morph_ex0 zXx (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1) Pi_2p0) with 
      Pi_2p1.
  rewrite <- assoc. 
  replace (compose z A' A (compose z A A' h m) r) with
    (compose _ _ _ h (compose _ _ _ m r)). compute in H. rewrite H.
  rewrite id_unit_left. exact H2.
  rewrite assoc. auto. 
  compute in pProd_morph_com_0. compute in pProd_morph_com_3.
  assert ((rc _ _ (compose zXx aXx' x
  (pProd_morph_ex0 zXx
     (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1)
  Pi_2p0)) = (id _ )). rewrite rc_d. compute.
  compute in Pi_2Tot0. rewrite Pi_2Tot0. rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  compute in Pi_2Tot1. rewrite Pi_2Tot1. rewrite id_unit_right.
  rewrite rc_d. compute. compute in rc_d.
  rewrite (rc_d _ _ _ h m). compute in mIsTotal.
  rewrite (mIsTotal _ _ m r H). rewrite id_unit_left.
  compute in H1. rewrite H1. rewrite id_unit_left.
  compute in Pi_1Tot1. rewrite Pi_1Tot1. auto. 
  transitivity (compose _ _ _ (rc zXx x
       (compose zXx aXx' x
          (pProd_morph_ex0 zXx (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1)
          Pi_2p0)) Pi_2p1).
  rewrite H4. rewrite (id_unit_right _ _ Pi_2p1). auto.
  rewrite pProd_morph_com_3. auto.

  compute in pProd_morph_com_0. 
  assert ((rc _ _ (compose zXx aXx' A'
  (pProd_morph_ex0 zXx
     (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1)
  Pi_1p0)) = (id _ )). rewrite rc_d. compute.
  compute in Pi_1Tot0. rewrite Pi_1Tot0. rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  compute in Pi_2Tot1. rewrite Pi_2Tot1. rewrite id_unit_right.
  rewrite rc_d. compute. compute in rc_d.
  rewrite (rc_d _ _ _ h m). compute in mIsTotal.
  rewrite (mIsTotal _ _ m r H). rewrite id_unit_left.
  compute in H1. rewrite H1. rewrite id_unit_left.
  compute in Pi_1Tot1. rewrite Pi_1Tot1. auto. 
  transitivity (compose _ _ _ (rc zXx A'
       (compose zXx aXx' A'
          (pProd_morph_ex0 zXx (compose zXx z A' Pi_1p1 (compose z A A' h m)) Pi_2p1)
          Pi_1p0)) (compose zXx z A' Pi_1p1 (compose z A A' h m))).
  rewrite H4. rewrite id_unit_right. auto.
  rewrite pProd_morph_com_0. auto.
Defined.


Definition embedding_computable `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) (bullet : Hom (RCat_HP A A) A) :
exists m, exists (p_r : point rco A),
  ((bullet ∘ (@pProd_morph_ex CRC rco CRC  _ _ _ (RCat_HP A A) ((proj1_sig p_f) ∘ (pt_morph (RCat_HP A A))) 
    (bullet ∘ (@pProd_morph_ex CRC rco CRC  _ _ _ A ))) ∘ m = id (RCat_HP A A)).

Definition points_turing `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  : forall (bullet : Hom (RCat_HP A A) A) ,
((forall a : CRC, @embedding_computable CRC a A bullet) /\
((exists (h : Hom A A), (TotMaps rco CRC A A h) /\ 
  ((bullet ∘ (@pProd_morph_ex CRC rco CRC  _ _ _ (RCat_HP A A) (h ∘ Pi_1p) (Pi_2p))) = bullet)) /\ (forall (f : Hom A A),  (exists (p_f : point rco A), 
  ((bullet ∘ (@pProd_morph_ex CRC rco CRC  _ _ _ A ((proj1_sig p_f) ∘ (pt_morph A)) (id A))) = f))))
  -> (CompMorph C rco RC CRC A bullet)).
intros. unfold CompMorph. intros.
destruct H. destruct H0.
destruct H0. destruct H0.
destruct (H (RCat_HP A A)) as [m].
destruct H3 as [r]. 
destruct (H1 ( f ∘ r ∘ bullet ∘ r)).
exists x.  
destruct CRC. destruct RC. destruct rco. destruct C. destruct RCat_RC.
destruct RCat_HP. simpl. replace f with ((f ∘ r) ∘ m). rewrite <- H4. simpl.
rewrite H2.
rewrite H4.  rewrite <- H2.

 rewrite H2. simpl in f. simpl in r. 
eexists .  Focus 2. 

exists (proj1_sig x ∘ pt_morph A). split.
Focus 2.
replace f with ((f ∘ r) ∘ m).
rewrite <- H2. rewrite assoc.
rewrite ProdMapComp.
replace (pProd_morph_ex A (proj1_sig x ∘ pt_morph A) id ∘ m) with 
(pProd_morph_ex (RCat_HP A A)
    ((proj1_sig x ∘ pt_morph A) ∘ Pi_1p) Pi_2p).
*)

(exists (h : Hom A A), (TotMaps rco CRC A A h) /\ 
  ((bullet ∘ (@pProd_morph_ex CRC rco CRC  _ _ _ (RCat_HP A A) (h ∘ Pi_1p) (Pi_2p))) = bullet))

(* The Halting set is m-complete *)
Lemma halting_m_comp `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(A : CRC) `{ T : @TuringCat C rco RC CRC A }  : 
    forall  (X : T) (bullet : Hom (RCat_HP A A) A) (tm : @TuringMorph T rco T T A T bullet ) (e : Hom X X) , e = (rc _ _ e)  -> 
         (exists (f : Hom X (RCat_HP A A)), ((rc _ _ f ) = (id X)) /\ (rc _ _ e) = (rc _ _ ((rc _ _ bullet) ∘ f))).
Proof. 
  intro X.
  generalize (everyObjisRetract rco A X). intro retX. 
  generalize mIsTotal. intro mIsTotal. 
  generalize IdIsTotal. intro IdIsTotal.
  destruct retX as [m]. destruct H as [r]. 

  generalize (ProdMapComp CRC). intro ProdMapComp. destruct CRC. 
  generalize (fun X Y => ProdMapComp A A X Y (Restriction.RCat_HP A A)).

  destruct RC; destruct C. unfold RCat_RC. assert (rccato : RCat_RC = rco). auto.
  rewrite rccato in rc_d.
  destruct RCat_RC. destruct rco. 
  unfold TuringMorph. destruct T.
  compute. intros pmcA. intros  bullet tm e. 

  destruct (RCat_HP A A) as [AxA p1 p2 pt1 pt2 px]. destruct RCat_term.
  compute in p_term. 
  generalize  ( (tm p_term (RCat_HP p_term A))).
  destruct  (RCat_HP p_term A) as [txA pta1 pta2 ptt1 ptt2 ptx]. intro tmtA.
  destruct (tmtA ( (m ∘ e ∘ r)  ∘ pta2 )) as [c_mer]. 
  destruct H0 as [tot comp]. intros.

  exists ((px _ (c_mer ∘ (pt_morph A)) (id A)) ∘ m). 
  split. Focus 2. transitivity (rc0 X A (compose _ _ _ e m)).
  compute in rc_d.  rewrite (rc_d _ _ _ e m).
  compute in mIsTotal. 
  rewrite (mIsTotal  _ _ m r H). rewrite id_unit_left. auto.
  compute in comp. rewrite <- rc_d. compute. 
  transitivity 
  (rc0 _ _ (compose _ _ _ (compose _ _ _  m (compose _ _ _ (ptx _ (pt_morph A) (id A)) pta2 )) 
       (compose A X A (compose A X X r e) m))).
  compute in pProd_morph_com_3.
  replace (compose A txA A (ptx A (pt_morph A) (id A)) pta2) with (id A).
  rewrite id_unit_left. rewrite assoc. rewrite assoc. compute in H. rewrite H.
  rewrite id_unit_right. auto. 
  transitivity (compose A A A (rc0 A A (compose A txA A (ptx A (pt_morph A) (id A)) pta2)) (id A)).
  compute in pProd_morph_rest0. compute in rc_d. rewrite rc_d.
  compute in ptt2. rewrite ptt2. rewrite id_unit_left.
  rewrite id_unit_left. rewrite <- pProd_morph_rest0.
  rewrite morph_total. compute. rewrite id_unit_left.
  rewrite IdIsTotal. compute. auto.
  rewrite pProd_morph_com_3. auto.
  rewrite <- assoc. rewrite <- assoc. 
  rewrite comp. rewrite assoc. rewrite pmcA. rewrite assoc.
  assert ((compose X txA AxA 
      (compose X A txA m (ptx A (pt_morph A) (id A)))
      (px txA (compose txA p_term A pta1 c_mer) pta2)) = px X 
      (compose X A A m (compose A p_term A (pt_morph A) c_mer))
      (compose X A A m (id A))). 

  rewrite <- assoc. rewrite (pmcA txA). rewrite pmcA. 
  compute in pProd_morph_com_3 . rewrite <- pProd_morph_com_3.
  rewrite assoc. rewrite assoc.
  replace ((compose X txA p_term 
      (compose X A txA m (ptx A (pt_morph A) (id A))) pta1)) with 
    (compose _ _ _ m (compose _ _ _ (ptx A (pt_morph A) (id A)) pta1)).
  compute in pProd_morph_com_0 . rewrite <- (pProd_morph_com_0 ).
  replace ((rc0 A p_term (compose A txA p_term (ptx A (pt_morph A) (id A)) pta1))) with (id A).
  replace (rc0 A A (compose A txA A (ptx A (pt_morph A) (id A)) pta2))  with (id A).
  rewrite id_unit_left. rewrite id_unit_right. rewrite assoc. auto.
  
  compute in rc_d. rewrite rc_d. compute in ptt2. rewrite ptt2. rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  rewrite IdIsTotal. rewrite morph_total. compute. rewrite id_unit_left. auto.
  
  compute in rc_d. rewrite rc_d. compute in ptt1. rewrite ptt1. rewrite id_unit_left.
  compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
  rewrite IdIsTotal. rewrite morph_total. compute. rewrite id_unit_left. auto.

  rewrite assoc. auto. rewrite H1. auto.

(* f is total *)
  compute in rc_d. rewrite rc_d. 
  compute in pProd_morph_rest. rewrite <- pProd_morph_rest.
  rewrite IdIsTotal. compute. rewrite id_unit_right.
  rewrite (rc_d _ _ _ (pt_morph A) c_mer). rewrite tot.
  rewrite id_unit_left.
  compute in morph_total. rewrite morph_total. compute in mIsTotal.
  rewrite rc_d. rewrite IdIsTotal. compute. rewrite id_unit_left.
  rewrite (mIsTotal X  A m r H). auto.
Defined.


(* (A, bullet) is a combinatory complete applicative system whenever it is a universal application in a CRC *)
Definition TurMorph_combComp  `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : forall (bullet : Hom (RCat_HP A A) A) ,
    (CompMorph C rc RC CRC A bullet)  <-> (AppSysIsCombComp A bullet).
Proof.
(*
  unfold AppSysIsCombComp. unfold isAppStructForn.
  split; intros. induction lf. destruct n. destruct C. 
  unfold isAppStructTerm. simpl.
  compute in f_t. destruct CRC. destruct RCat_term. compute.
  eexists. destruct ?p. destruct RC. destruct rc.
  eexists. rewrite pt_morph_unique_greatest. compute.
  unfold TxyUniv in H. unfold fAdmitsTxy in H.
  elim (H p_term (RCat_HP p_term A)  (compose _ _ _  (compose _ _ _ (@Pi_1p _ _ _ p_term A  (RCat_HP p_term A)) f_t) x) ).
  compute. intros x0 admits. destruct admits. 
  destruct (RCat_HP p_term A) as [AxA]. destruct RCat_HP.




Focus 2.
  destruct RC. destruct rc. destruct CRC. destruct RCat_term. destruct C.
  destruct n. simpl. unfold f_comp. eexists. split. compute.
  destruct (RCat_HP A p_term) as [Ax1]. destruct (RCat_HP) as [AxA]. *)

Admitted.


(* define the embedding of CompA into Turing Cat T *)
Definition Comp_tur_o `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
:  @Obj (CompA_CRCat CRC rco CRC CRC A) ->   @Obj  T .
unfold CompA_CRCat. simpl. intro. destruct X as [a]. exact a.
Defined.


Definition Comp_tur_m `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) :
∀ a b, @Hom (CompA_CRCat CRC rco CRC CRC A) a b -> @Hom T (Comp_tur_o _ _ _ _ _ _ a) (Comp_tur_o _ _ _ _ _ _ b) .
intros. unfold Comp_tur_o. simpl. destruct a as [a]. destruct b as [b]. destruct X as [f].
simpl in f. exact f.
Defined.

Definition Comp_T_Emb_Func `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) : 
   Functor (CompA_CRCat CRC rco CRC CRC A) T.
exists (Comp_tur_o _ rco _ _ _ _) (Comp_tur_m _ rco _ _ _ _).
intro. unfold Comp_tur_m. destruct c as [c]. simpl. auto.
intros. unfold Comp_tur_m. destruct f as [f]. destruct g as [g].
destruct a as [a]. destruct b as [b]. destruct c as [c].
simpl. auto.
Defined.

Definition Comp_T_Emb_Faithful `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) : 
Faithful_Func (Comp_T_Emb_Func _ rco _ _ _ _).
unfold Faithful_Func. intros.
destruct c as [c]. destruct c' as [c']. simpl in H.
destruct h as [h]. destruct h' as [h']. simpl.
rewrite H. apply pf_ir.
Defined.

Definition Comp_T_Emb_Full `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) : Full_Func (Comp_T_Emb_Func _ rco _ _ _ _).
unfold Full_Func. intros c c' h'.
destruct c as [c]. destruct c' as [c'].
simpl in h' . simpl. 
exists (exist (fun (x : Hom c c') => True) h' I ). auto.
Defined.

Instance Comp_T_Embedding `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) : Embedding (CompA_CRCat CRC rco CRC CRC A) T.
exists (Comp_T_Emb_Func _ rco _ _ _ _). exact (Comp_T_Emb_Faithful _ rco _ _ _ _).
exact (Comp_T_Emb_Full _ rco _ _ _ _).
Defined.

Definition TurSpCompA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) : (CompA_CRCat CRC rco CRC CRC A) .
unfold CompA_CRCat. simpl. exists (RCat_HP A RCat_term ). exists 1. simpl. auto.
Defined.

(* given a collection of specific embedding-retraction pairs for all objects in Turing category T,
   can define and embedding of T into SplitCompA *)
(* note that is has been proven earlier that such a collection EXISTS *)

(* define the embedding of Turing cat T into SplitCompA *)
Definition Tur_spcompA_o `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
  (emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } )
: forall (emb_o : @Obj T ),  @Obj  (SplitCompA_justCat_allIdem CRC rco CRC CRC A).
intro.
unfold SplitCompA_justCat_allIdem. unfold SplitCRC. simpl.
 unfold split_obj. unfold CompA_CRCat. simpl. unfold all_split.
destruct ( emb_col emb_o) as [mr Hmr]. destruct mr as [m r].
eexists ((exist (fun (x : CRC) => (∃ n : nat, x = nthProdC rco A n)) (RCat_HP A RCat_term) _ )). 
simpl.
eexists (exist (fun (_ : Hom (RCat_HP A RCat_term) (RCat_HP A RCat_term)) => True)
   (@pProd_morph_ex _ _ _ A RCat_term (RCat_HP A RCat_term) (RCat_HP A RCat_term) ((m ∘ r) ∘ Pi_1p) (Pi_2p)) I ).
simpl. split. auto.
apply exist_eq. rewrite (ProdMapComp CRC).
rewrite assoc. destruct RCat_term. simpl.
generalize (fun (d c : CRC) => ProdMapComp CRC A p_term d c (RCat_HP A p_term)). intro PMC.
destruct (RCat_HP A p_term) as [Ax1]. simpl.
destruct RC.
replace RCat_RC with rco in rc_d.
destruct rco. destruct C. destruct CRC.  simpl in rc_d.
compute in pProd_morph_com_2. compute in pProd_morph_com_1.
compute. rewrite <- pProd_morph_com_1. rewrite <- pProd_morph_com_2.
rewrite rc_d. simpl in Pi_1Tot. rewrite Pi_1Tot. rewrite id_unit_left.
rewrite rc_d. simpl in Pi_2Tot. rewrite Pi_2Tot. rewrite id_unit_left.
compute in PMC. rewrite <- assoc. rewrite <- assoc.
replace (compose A A A (compose A emb_o A r m) (compose A emb_o A r m)) with (compose A emb_o A r m).
 rewrite <- PMC. rewrite  rc1. auto. rewrite <- (assoc _ _ _ _ _ m ).
replace (compose emb_o A A m (compose A emb_o A r m)) with (compose _ _ _ (compose _ _ _ m r) m).
compute in Hmr. rewrite Hmr. rewrite id_unit_right. auto.
rewrite assoc. auto. auto.
Unshelve. simpl. exists 1. simpl. auto. 
Defined. 


Definition Tur_spcompA_m `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
 (emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } )
(a b : @Obj T) (f : @Hom T a b) : @Hom (SplitCompA_justCat_allIdem CRC rco CRC CRC A) 
(Tur_spcompA_o T rco T T A T emb_col a) (Tur_spcompA_o T rco T T A T emb_col b).
unfold Tur_spcompA_o. 
destruct (emb_col a) as [mr Hmr].
destruct (emb_col b) as [mrb Hmrb]. simpl.
unfold split_hom; unfold all_split; simpl.
destruct mr as [ma ra]; destruct mrb as [mb rb]; simpl.
generalize (ProdMapComp CRC A RCat_term (RCat_HP A RCat_term) (RCat_HP A RCat_term) (RCat_HP A RCat_term) ); 
intro ProdMapComp.
destruct  (RCat_HP A RCat_term) as [Ax1]. simpl.
eexists (exist (fun (x : Hom Ax1 Ax1) => True) 
 (pProd_morph_ex Ax1 (mb ∘ f ∘ ra ∘ Pi_1p) Pi_2p ) I ).
split; apply exist_eq; simpl; rewrite ProdMapComp; simpl;
rewrite assoc; generalize (@mIsTotal C rco RC); intro mistot;
destruct C; destruct RC; replace RCat_RC with rco in rc_d;
destruct rco; destruct CRC; compute in pProd_morph_com_1;  compute;
destruct RCat_term; simpl. rewrite <-pProd_morph_com_1;
compute in pProd_morph_com_2; rewrite <- pProd_morph_com_2;
compute in pProd_morph_rest. 
compute in Pi_1Tot. compute in rc_d. rewrite rc_d.
rewrite Pi_1Tot. rewrite id_unit_left.
compute in Pi_2Tot. compute in rc_d. rewrite rc_d.
rewrite Pi_2Tot. rewrite id_unit_left.
rewrite (assoc _ _ _ _ _ rb mb). rewrite (assoc _ _ _ _ _ _ mb).
rewrite <- (assoc _ _ _ _ _ mb rb).
 compute in Hmrb.  rewrite Hmrb. rewrite id_unit_left.
rewrite <- assoc. rewrite <- ProdMapComp. simpl.
rewrite rc1. auto. auto. 
compute in pProd_morph_com_2; rewrite <- pProd_morph_com_2;
compute in pProd_morph_rest. 
compute in Pi_2Tot. compute in rc_d. rewrite rc_d.
rewrite Pi_2Tot. rewrite id_unit_left. rewrite assoc. rewrite assoc.
rewrite <-pProd_morph_com_1.
compute in Pi_1Tot. compute in rc_d. rewrite rc_d.
rewrite Pi_1Tot. rewrite id_unit_left.
rewrite (assoc _ _ _ _ _ ra ma). rewrite (assoc _ _ _ _ _ _ ma).
rewrite <- (assoc _ _ _ _ _ ma ra).
 compute in Hmr.  rewrite Hmr. rewrite id_unit_left.
rewrite <- assoc. compute in ProdMapComp.
rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
rewrite <- pProd_morph_rest. rewrite Pi_2Tot. rewrite id_unit_right.
replace ((compose Ax1 a A (compose Ax1 A a Pi_1p ra) (compose a b A f mb))) with 
(compose Ax1 A A Pi_1p (compose A a A ra (compose a b A f mb))).
rewrite <-ProdMapComp.
rewrite <- (rc1 _ _ (pProd_morph_ex Ax1 (compose Ax1 A A Pi_1p (compose A a A ra (compose a b A f mb))) Pi_2p)). compute.
rewrite <- pProd_morph_rest. rewrite Pi_2Tot. rewrite id_unit_right.
rewrite (assoc _ _ _ _ (rc Ax1 A (compose Ax1 a A (compose Ax1 A a Pi_1p ra) ma)) _ _). 
replace ( (compose Ax1 Ax1 Ax1 (rc Ax1 A (compose Ax1 a A (compose Ax1 A a Pi_1p ra) ma))
     (rc Ax1 A (compose Ax1 A A Pi_1p (compose A a A ra (compose a b A f mb)))))) with 
     (rc Ax1 A (compose Ax1 A A Pi_1p (compose A a A ra (compose a b A f mb)))).
auto. compute.
rewrite (rc_d _ _ _ _ ma). compute in mistot. rewrite (mistot _ _ ma ra Hmr).
rewrite (assoc _ _ _ _ Pi_1p). rewrite id_unit_left.
rewrite <- rc3. compute.
replace (compose Ax1 Ax1 A (rc Ax1 a (compose Ax1 A a Pi_1p ra))
     (compose Ax1 a A (compose Ax1 A a Pi_1p ra) (compose a b A f mb))) with
(compose _ _ _ (compose _ _ _ (rc Ax1 a (compose Ax1 A a Pi_1p ra))(compose Ax1 A a Pi_1p ra)) (compose a b A f mb)).
rewrite rc1. auto. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. auto.
 rewrite assoc. auto. auto.
Defined.


Definition Sp_Comp_T_Fuct_pfs  `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
(emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } ) : 
(∀ c : T, Tur_spcompA_m C rco RC CRC A T emb_col c c id = id )
/\
(∀ (a b c : T) (f : Hom a b) (g : Hom b c),
Tur_spcompA_m C rco RC CRC A T emb_col a c (g ∘ f) =
Tur_spcompA_m C rco RC CRC A T emb_col b c g
∘ Tur_spcompA_m C rco RC CRC A T emb_col a b f).
Admitted.

Definition Sp_Comp_T_Fuct `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
(emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } ) : 
  Functor  T (SplitCompA_justCat_allIdem C rco RC CRC A).
exists (Tur_spcompA_o C rco RC CRC A T emb_col ) (Tur_spcompA_m C rco RC CRC A T emb_col ).
exact (proj1 (Sp_Comp_T_Fuct_pfs C rco RC CRC A T emb_col)).
exact (proj2 (Sp_Comp_T_Fuct_pfs C rco RC CRC A T emb_col)).
Defined.

(*
destruct CompA_CRCat. destruct (SplitCompA_justCat_allIdem C rco RC CRC A).
unfold Tur_spcompA_o; simpl.
unfold all_split; simpl. unfold split_hom; simpl.
intro c. destruct (emb_col c) as [mr Hmr].
destruct (Restriction.RCat_HP A Restriction.RCat_term) as [Ax1]. simpl.
destruct T. destruct CRC. destruct RC. destruct C. simpl. 
unfold Tur_spcompA_o. unfold split_id. simpl. destruct CompA_CRCat.
intro. generalize dependent (id (Tur_spcompA_o _ _ _ _ _ _ emb_col c)). elim T.
destruct (emb_col c). destruct x as [mc rc]. simpl in e. intros.
destruct h. unfold Tur_spcompA_m. simpl. unfold all_split.
destruct x. destruct (emb_col c). simpl.
destruct CRC. destruct C.
destruct (Tur_spcompA_m _ _ _ _ _ _ emb_col c c id) as [f_t].
apply exist_eq.
destruct ((Tur_spcompA_o _ _ _ _ _ _ emb_col c)) as [comp_c].
destruct s as [ec]. intro. simpl. unfold all_split. intro. destruct h. 
destruct (Tur_spcompA_m C rco RC CRC A {| AisTuring := AisTuring0 |}
  emb_col c c id). apply exist_eq. destruct a2. simpl in H.
destruct x0. destruct x. apply exist_eq. inversion H0. inversion H.
destruct ((Tur_spcompA_o _ _ _ _ _ _ emb_col c)). simpl.
simpl in f_t. simpl.
unfold Tur_spcompA_m.
unfold CompA_CRCat.  simpl.
unfold split_id.
destruct id. rewrite exist_eq.
exact (Comp_T_Emb_Faithful _ rco _ _ _ _).
exact (Comp_T_Emb_Full _ rco _ _ _ _).
Defined. *)


Definition Sp_Comp_T_Emb_Faithful `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
(emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } ) : 
Faithful_Func (Sp_Comp_T_Fuct _ rco _ _ _ _ emb_col).
Admitted.

Definition Sp_Comp_T_Emb_Full `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
(emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } )
: Full_Func (Sp_Comp_T_Fuct _ rco _ _ _ _ emb_col).
Admitted.

Instance Sp_Comp_T_Embedding `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
(emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } ) :
Embedding T (SplitCompA_justCat_allIdem CRC rco CRC CRC A) .
exists (Sp_Comp_T_Fuct _ rco _ _ _ _ emb_col). exact (Sp_Comp_T_Emb_Faithful _ rco _ _ _ _ emb_col).
exact (Sp_Comp_T_Emb_Full _ rco _ _ _ _ emb_col).
Defined.


(*  an equivalent to the definition characterization of Turing categories  *)
Definition eq_charac `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  :
(exists (bullet : Hom (RCat_HP A A) A) , CompMorph C rco RC CRC A bullet) ->
(forall a, @isRetractOf C a A) -> @TuringObj CRC rco CRC CRC A.
intros. destruct H as [bullet]. unfold CompMorph in H.
unfold TuringObj . intros. destruct aXx as [aXx]. simpl.
unfold TxyUniv. unfold fAdmitsTxy. 
generalize (fun  xx yy => ProdMapComp CRC A A xx yy (RCat_HP A A)). intro pmcAA.
destruct (H0 x) as [m hmr].
destruct (H0 y) as [my hmry].
destruct hmr as [rx hmrx]. destruct hmry as [ry hmry].
destruct ( RCat_HP A A) as [AxA].
exists (ry ∘ bullet ∘ (pProd_morph_ex0 aXx Pi_1p (m ∘ Pi_2p))).
simpl in H. intros. 
destruct (H0 z) as [mz hmrz].
destruct hmrz as [rz hmrz].
generalize (fun  xx yy => ProdMapComp CRC z x xx yy zXx). intro pmczx.
destruct zXx as [zXx]. simpl.
destruct (H (my ∘ f ∘ (pProd_morph_ex1 AxA (rz ∘ Pi_1p0) (rx ∘ Pi_2p0)))) as [f_AA].
exists (f_AA ∘  mz).
generalize (IdIsTotal ); simpl; intro idist.
 split. destruct H1. simpl. unfold TotMaps.
generalize (mIsTotal _ _ mz rz hmrz).
destruct C; destruct RC; destruct CRC. replace RCat_RC with rco in rc_d . 
simpl in pProd_morph_com_0; simpl in pProd_morph_com_3.
replace RCat_RC with rco in pProd_morph_com_0; replace RCat_RC with rco in pProd_morph_com_3; 
replace RCat_RC with rco in pProd_morph_com_4; replace RCat_RC with rco in pProd_morph_com_4; 
replace RCat_RC with rco in pProd_morph_com_1; replace RCat_RC with rco in pProd_morph_com_2; try auto.
destruct rco.
simpl. intros. rewrite rc_d. simpl. compute in H1. rewrite H1. rewrite id_unit_left.
auto. auto. destruct H1. simpl in pmcAA. simpl in pmczx. 
rewrite assoc. rewrite assoc.
rewrite pmcAA. 
replace f with (ry ∘ (my ∘ f ∘ pProd_morph_ex1 AxA (rz ∘ Pi_1p0) (rx ∘ Pi_2p0)) ∘
        pProd_morph_ex0 zXx (mz ∘ Pi_1p1) (m ∘ Pi_2p1)).
rewrite H2. Focus 2. rewrite assoc. rewrite assoc.
rewrite pmczx. rewrite assoc.
assert (Pi_1p0 ∘ pProd_morph_ex0 zXx (mz ∘ Pi_1p1) (m ∘ Pi_2p1) = (mz ∘ Pi_1p1)).
 destruct C. destruct RC. replace RCat_RC with rco in rc_d . destruct rco. compute. compute in pProd_morph_com_0.
 rewrite <- pProd_morph_com_0. rewrite rc_d. simpl. 
compute in Pi_1Tot0 . rewrite Pi_1Tot0. rewrite id_unit_left.
compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
rewrite <- assoc. rewrite rc1. rewrite rc_d. simpl.
generalize (mIsTotal _ _  m rx hmrx); simpl; intro mtx; rewrite mtx.
rewrite id_unit_left. 
compute in Pi_2Tot1 . rewrite Pi_2Tot1. rewrite id_unit_right. auto. auto.
rewrite assoc.
assert ( (Pi_2p0 ∘ pProd_morph_ex0 zXx (mz ∘ Pi_1p1) (m ∘ Pi_2p1)) = (m ∘ Pi_2p1)).
 destruct C. destruct RC. replace RCat_RC with rco in rc_d . destruct rco. compute. compute in pProd_morph_com_3.
 rewrite <- pProd_morph_com_3. rewrite rc_d. simpl. 
compute in Pi_2Tot0 . rewrite Pi_2Tot0. rewrite id_unit_left.
compute in pProd_morph_rest0. rewrite <- pProd_morph_rest0.
rewrite rc2. compute.
rewrite <- assoc. rewrite rc1. rewrite rc_d. simpl.
generalize (mIsTotal _ _  mz rz hmrz); simpl; intro mtx; rewrite mtx.
rewrite id_unit_left. 
compute in Pi_1Tot1 . rewrite Pi_1Tot1. rewrite id_unit_right. auto. auto.
compute in H3. destruct C. compute. rewrite H3. compute in H4. rewrite H4.
compute in assoc. rewrite <- assoc. compute in hmry. rewrite hmry.
rewrite id_unit_left. rewrite <- assoc. compute in hmrz; rewrite hmrz.
rewrite id_unit_left. rewrite <- assoc. compute in hmrx; rewrite hmrx.
rewrite id_unit_left. 
replace ( (pProd_morph_ex1 zXx Pi_1p1 Pi_2p1)) with (id zXx).
rewrite id_unit_right. auto. compute in pProd_morph_unique1. 
destruct RC. replace RCat_RC with rco in pProd_morph_unique1; 
replace RCat_RC with rco in rc_d; try auto.
destruct rco. destruct RCat_RC. apply pProd_morph_unique1; simpl in rc_d;
try (rewrite rc_d); simpl in Pi_1Tot1; simpl in Pi_2Tot1; 
try (rewrite id_unit_right); try (rewrite id_unit_left);
try (rewrite Pi_1Tot1);
 try (rewrite Pi_2Tot1);
try (rewrite id_unit_right); try (rewrite id_unit_left);
 try (rewrite idist); compute;
try (rewrite id_unit_right); try (rewrite id_unit_left); try auto.
 destruct C. destruct RC. replace RCat_RC with rco in rc_d . destruct rco. compute. 
rewrite  assoc. compute in pmcAA. rewrite pmcAA.
replace ((compose zXx aXx A
           (pProd_morph_ex zXx
              (compose zXx z A Pi_1p1 (compose z A A mz f_AA)) Pi_2p1)
           Pi_1p)) with (compose zXx AxA A  (pProd_morph_ex0 zXx  (compose zXx z A Pi_1p1 mz) 
              (compose zXx x A Pi_2p1 m))   (compose AxA A A Pi_1p0 f_AA)).
replace ((compose zXx aXx A
           (pProd_morph_ex zXx
              (compose zXx z A Pi_1p1 (compose z A A mz f_AA)) Pi_2p1)
           (compose aXx x A Pi_2p m))) with (compose zXx AxA A
           (pProd_morph_ex0 zXx 
              (compose zXx z A Pi_1p1 mz) 
              (compose zXx x A Pi_2p1 m)) Pi_2p0). auto.
compute in pProd_morph_com_3. rewrite <- pProd_morph_com_3. simpl in rc_d.
rewrite rc_d; compute in Pi_2Tot0; try (rewrite Pi_2Tot0).
rewrite id_unit_left. compute in pProd_morph_rest0; rewrite <- pProd_morph_rest0.
rewrite rc_d. generalize (mIsTotal _ _  m rx hmrx); simpl; intro mtx; rewrite mtx.
rewrite id_unit_left.
rewrite rc_d. generalize (mIsTotal _ _  mz rz hmrz); simpl; intro mtz; rewrite mtz.
rewrite id_unit_left.
compute in Pi_2Tot1; rewrite Pi_2Tot1. 
compute in Pi_1Tot1; rewrite Pi_1Tot1. rewrite id_unit_left. rewrite id_unit_right.
rewrite assoc.
compute in pProd_morph_com_2. rewrite <- pProd_morph_com_2. simpl in rc_d.
rewrite rc_d; compute in Pi_2Tot; try (rewrite Pi_2Tot).
rewrite id_unit_left. compute in pProd_morph_rest; rewrite <- pProd_morph_rest.
rewrite rc_d. compute in Pi_2Tot1; try (rewrite Pi_2Tot1). 
rewrite id_unit_right. rewrite (rc_d z A A _ _ ). compute in H1. rewrite H1.
rewrite id_unit_left. rewrite mtz. rewrite id_unit_left.
compute in Pi_1Tot1; try (rewrite Pi_1Tot1). 
rewrite id_unit_right. auto.
compute in pProd_morph_com_1. rewrite <- pProd_morph_com_1. simpl in rc_d.
rewrite rc_d. compute in Pi_1Tot; try (rewrite Pi_1Tot).
rewrite id_unit_left. compute in pProd_morph_rest; rewrite <- pProd_morph_rest.
compute in Pi_2Tot1; try (rewrite Pi_2Tot1). rewrite id_unit_right.
rewrite rc_d. rewrite (rc_d z A A _ _).  compute in H1. rewrite H1.
rewrite id_unit_left. generalize (mIsTotal _ _  mz rz hmrz); simpl; intro mtz; rewrite mtz.
rewrite id_unit_left. compute in Pi_1Tot1; try (rewrite Pi_1Tot1). rewrite id_unit_right.
rewrite assoc. compute in pProd_morph_com_0. rewrite <- pProd_morph_com_0.
rewrite rc_d. compute in Pi_1Tot0; try (rewrite Pi_1Tot0). 
rewrite id_unit_left. compute in pProd_morph_rest0; rewrite <- pProd_morph_rest0.
rewrite rc_d. generalize (mIsTotal _ _  m rx hmrx); simpl; intro mtx; rewrite mtx.
rewrite id_unit_left. compute in Pi_2Tot1; try (rewrite Pi_2Tot1).
rewrite rc_d. rewrite mtz. rewrite id_unit_left.  compute in Pi_1Tot1; try (rewrite Pi_1Tot1).
rewrite id_unit_left. rewrite id_unit_right. rewrite assoc. auto. auto.
Defined.


(*
(* CompA is a cartesion restriction category which contains a PCA (A, bullet) and every
other object is a retract of A *)
Class CompACat `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : Type :=
{
  comp_cat : @CartRestrictionCat (all_prod_maps_Rcat C rco RC CRC A) (rcCompA C rco RC CRC  A) (all_prod_maps_Rcat C rco RC CRC A)
  :=  CompA_CRCat  C rco RC CRC A  ;
  is_comb_complete : exists (bullet : Hom (RCat_HP A A) A), (TxyUniv A A A (RCat_HP A A) bullet)
}.


(* define formal idempotent splitting on a category *)
Coercion comp_cat : CompACat >-> CartRestrictionCat.


(* given a Turing category with Turing object A, 
  CompA is a full (Turing) *)
(* comp(A) is a Turing category for any PCA (A, bullet) *)
Definition compATuring  `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A )  (E : idem_class (CompA_CRCat CRC rco CRC CRC A))
  (pfe_cl : E_closed_prod _ _ _ _ E ) ( Ehas_id : E RCat_term (id RCat_term) )  (bullet : Hom (RCat_HP A A) A) :
   @TuringCat C rco RC CRC A  -> @TuringCat CompA rcCompA CompA CompA (S 0).
Proof.
(* given a Turing category with Turing object A, 
  it is a full (Turing) subcategory of the Turing Category splitCompA *)
Instance `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A )  (E : idem_class (CompA_CRCat CRC rco CRC CRC A))
  (pfe_cl : E_closed_prod _ _ _ _ E ) ( Ehas_id : E RCat_term (id RCat_term) )
  split_comp_cat
  :=  SplitCRC (CompA_CRCat CRC rco CRC CRC A) (rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) 
      E pfe_cl Ehas_id ;
(SCA : (SplitCompACat CRC rco CRC CRC A)), @Obj  SCA -> 
    @Obj T.
intro. destruct SCA. simpl. unfold split_obj. intro a. 
destruct a as [a]. simpl in a. destruct a as [a].  exact a.
Defined.

(* the class of comb. complete CRCs of CompA with a class E of idempotents split *)
Class SplitCompACat `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : Type :=
{
  E : idem_class (CompA_CRCat CRC rco CRC CRC A) ;
  pfe_cl : E_closed_prod _ _ _ _ E ;
  Ehas_id : E RCat_term (id RCat_term) ;
  split_comp_cat
  :=  SplitCRC (CompA_CRCat CRC rco CRC CRC A) (rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) 
      E pfe_cl Ehas_id ;
  is_comb_comp_sp : exists (bullet : Hom (RCat_HP A A) A), (TxyUniv A A A (RCat_HP A A) bullet)
}.


Coercion split_comp_cat : SplitCompACat >-> CartRestrictionCat.



Definition Fsp_tur_o `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A )
: forall (SCA : (SplitCompACat CRC rco CRC CRC A)), @Obj  SCA -> 
    @Obj T.
intro. destruct SCA. simpl. unfold split_obj. intro a. 
destruct a as [a]. simpl in a. destruct a as [a].  exact a.
Defined.


Definition Fsp_tur_m `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
: forall (SCA : (SplitCompACat CRC rco CRC CRC A)), 
∀ a b, @Hom SCA a b -> @Hom T (Fsp_tur_o _ _ _ _ _ _ _ a) (Fsp_tur_o _ _ _ _ _ _ _ b).
intros. destruct SCA. simpl. 
destruct a as [a]; destruct b as [b]. 
destruct X as [f]. simpl in f.
destruct a as [aa aaa]; destruct b as [bb bbb]. destruct s as [ea eea].
simpl in f; destruct f as [f ff]. apply f.
Defined.

Definition TotPar_Set_Cat_Eqv_b `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A )
: forall (SCA : (SplitCompACat CRC rco CRC CRC A)), @Obj  SCA -> 
    @Obj T.
intro. destruct SCA. simpl. unfold split_obj. intro a. 
destruct a as [a]. simpl in a. destruct a as [a].  exact a.
Defined.

Definition TotPar_Set_Cat_Eqv_b `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A )
: forall SCA : (SplitCompACat CRC rco CRC CRC A), Functor split_comp_cat T .
intro. destruct SCA. unfold split_comp_cat.
exists .
unfold Functor.

Lemma TotPar_Set_Cat_Eqv_o : Functor_compose  TotPar_Set_Cat_Eqv_f TotPar_Set_Cat_Eqv_b = Functor_id _.

Definition CompA_Tur `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall T : TuringCat rco A, 


Definition Fsp_tur_m `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC)  ( T : TuringCat rco A ) 
: forall (SCA : (SplitCompACat CRC rco CRC CRC A)), 
∀ a b, @Hom SCA a b -> @Hom T (Fsp_tur_o _ _ _ _ _ _ _ a) (Fsp_tur_o _ _ _ _ _ _ _ b).
intros. destruct SCA. simpl. 
destruct a as [a]; destruct b as [b]. 
destruct X as [f]. simpl in f.
destruct a as [aa aaa]; destruct b as [bb bbb]. destruct s as [ea eea].
simpl in f; destruct f as [f ff]. apply f.
Defined.


Open Scope nat_scope.



Definition paircrc `(CRC : CartRestrictionCat) (A : CRC) (n : nat) : prod CRC nat.
compute. exact (A, 

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

*)


