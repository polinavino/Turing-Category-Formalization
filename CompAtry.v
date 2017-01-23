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
Require Import Turing.
Require Import Par_Cat.

Generalizable All Variables. 


(* define a category all_prod_maps_cat as a full subcategory of the underlying CRC 
with objects 1, A, A^n, ... *)
Definition ObjCompAProp (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : CRC -> Prop :=
fun (x : CRC) => (exists (n : nat), x = (nthProdC rco A n)).

Instance all_prod_maps_cat (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : 
Category :=( Full_SubCategory C (ObjCompAProp CRC rco CRC CRC A)).


(* objects in CRC that are A^n are equal *)
Definition same_n_obj (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_cat C rco RC CRC A)) : Prop.
destruct a as [a ap]; destruct b as [b bp]. unfold ObjCompAProp in ap; unfold ObjCompAProp in bp.
exact ((∃ n : nat, (a = nthProdC rco A n) /\ (b = nthProdC rco A n )) -> (a = b)) . 
Defined.

Definition same_n_obj_pf (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_cat C rco RC CRC A)) : 
same_n_obj CRC rco CRC CRC A a b. 
unfold same_n_obj. 
destruct a as [a ap]; destruct b as [b bp]. unfold ObjCompAProp in ap; unfold ObjCompAProp in bp.
intro. destruct H as [n pf]. destruct pf as [pfa pfb]. rewrite pfa. rewrite pfb. auto.
Defined.

(* coercion to CRC objects 
Definition is_ob_inCRC `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : (nth_ProdT rc) -> CRC.
unfold nth_ProdT. simpl.
intro a. destruct a. exact x. Defined.

Instance CartRestrictionCatsAreCategories `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) `(CRC : @CartRestrictionCat C rc RC)  : RestrictionCat C rc := RC.

Coercion CartRestrictionCatsAreCategories : CartRestrictionCat >-> RestrictionCat.
*)

(* define a restriction combinator - inherited from underlying CRC *)
Definition rcCompAtype (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : rcType (all_prod_maps_cat C rco RC CRC A).
unfold rcType. destruct a as [a]; destruct b as [b]. simpl.
intro f; destruct f as [f]. exists (@rc RC rco a b f). auto. Defined.

Check (rcCompAtype Par_Cat rc_Par Par_isRC Par_isCRC nat) .


(*
Check rcCompAtype.
Definition rcType_compAis_rc `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) (rctype :  rcType (all_prod_maps_cat C rc RC CRC A)) : rcType CRC.
unfold all_prod_maps_cat in rctype. unfold rcType in rctype. simpl in rctype.
unfold rcType. intros.  *)

Definition rcCompA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC)  (A : CRC) : RestrictionComb (all_prod_maps_cat CRC rco CRC CRC A).
exists (rcCompAtype CRC rco CRC CRC A); intros; destruct a as [a]; try (destruct b as [b]);
try (destruct c as [c]); destruct f as [f]; try (destruct g as [g]); 
destruct C; destruct RC; destruct CRC; destruct rco; simpl; apply pf_ir. 
Defined.

(*
test definition of CompN RC directly
Definition CompN := (all_prod_maps_cat Par_Cat rc_Par Par_isRC Par_isCRC nat) .
Instance rcCompN : RestrictionComb CompN .
exists (rcCompAtype Par_Cat rc_Par Par_isRC Par_isCRC nat);
intros; 
destruct a as [a]; try (destruct b as [b]);
try (destruct c as [c]); destruct f as [f]; try (destruct g as [g]); 
simpl;  simpl in f; try (simpl in g). 
rewrite (@rc1 Par_Cat rc_Par). auto.
rewrite (@rc2 Par_Cat rc_Par). auto.
rewrite (@rc3 Par_Cat rc_Par). auto.
rewrite (@rc4 Par_Cat rc_Par). auto.
Defined.

Instance CompNR : RestrictionCat CompN rcCompN.
exists. Defined. *)


Definition all_prod_maps_Rcat (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) :=
RestrictionCat (all_prod_maps_cat _ _ _ _ A) (rcCompA _ _ _ _ A).

Check (all_prod_maps_Rcat ). Check (RestrictionComb (all_prod_maps_cat Par_Cat rc_Par Par_isRC Par_isCRC nat ) (rcCompA Par_Cat rc_Par Par_isRC Par_isCRC nat )).
Instance sdf : (all_prod_maps_Rcat Par_Cat rc_Par Par_isRC Par_isCRC nat) .

Definition A1toAtype `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc}
  `{CRC : @CartRestrictionCat C rc RC} (A : CRC) := (Hom (nthProdC rc A 1) A).

Definition AtoAtype `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc}
  `{CRC : @CartRestrictionCat C rc RC} (A : CRC) := (Hom A A).

Definition A1toAmap `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : A1toAtype A -> AtoAtype  A.
intro f. simpl in f. exact (compose _ _ _ _ (@pProd_morph_ex CRC rc CRC _ _ _ _ (id A) (pt_morph _))  f).
Defined.

Definition AtoA1map `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : AtoAtype A -> A1toAtype  A.
intro f. simpl in f. exact (compose _ _ _ _ Pi_1p  f).
Defined.

(*
Coercion AtoA1map : AtoAtype >-> A1toAtype.
*)

Definition A1toA1type `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc}
  `{CRC : @CartRestrictionCat C rc RC} (A : CRC) := (Hom (nthProdC rc A 1) (nthProdC rc A 1)).

Definition A1toA1map `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : A1toA1type A -> AtoAtype  A.
intro f. unfold A1toA1type in f. unfold AtoAtype. 
exact (compose _ _ _ _  (@pProd_morph_ex CRC rc CRC _ _ _ _ (id A) (pt_morph _)) (compose _ _ _ _ f Pi_1p ) )    .
Defined.

(* Coercion A1toA1map : A1toA1type >-> AtoAtype. *)

Definition AtoAmap `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : AtoAtype A ->  A1toA1type A.
intro f. unfold AtoAtype in f. unfold A1toA1type . 
exact (compose _ _ _ _ (compose _ _ _ _ Pi_1p f) (@pProd_morph_ex CRC rc CRC _ _ _ _ (id A) (pt_morph _))  )    .
Defined.

(* Coercion AtoAmap : AtoAtype  >-> A1toA1type. *)


Definition A11toA1map `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : A1toA1type A ->  A1toAtype A.
intro f. unfold A1toA1type in f. unfold A1toAtype . 
exact  (compose _ _ _ _ f Pi_1p )     .
Defined.

(* Coercion A11toA1map : A1toA1type  >-> A1toAtype. *)

(*  id A is computable implies id A^m is computable *)
Definition idm_comp `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  ( m : nat)  : (f_comp A bullet (S 0) (A11toA1map _ _ _ _ A (@id _ (nth_Prod_obj rco (nthProdC rco A 1))))) -> 
  isAppStructFornProd A bullet m m (id (nthProdC rco A m) ).
unfold isAppStructFornProd. unfold isAppStructFornProd_test_m.
induction m; unfold f_comp; simpl; intro H; destruct H as [p pf]; 
destruct pf as [pf1 pf2]. exists p. rewrite assoc.
unfold A11toA1map in pf1.



Focus 2. simpl. induction m. simpl. split.
unfold f_comp. simpl. exists p. split.
unfold A11toA1map in pf1. destruct rco. destruct RC. destruct RCat_RC.
simpl. 

Focus 2. intro; tauto.
Focus 3. simpl. split. (*
rewrite rc_d.
replace (rc (RCat_HP A RCat_term) RCat_term (Pi_2p ∘ id)) with (id (RCat_HP A RCat_term)).

replace (bullet_n A 1 bullet) with  (Pi_1p ∘ (bulletn_once  A 0 bullet)) in pf1.
unfold bulletn_once in pf1. unfold projto_2ndA in pf1. unfold projto_restAs in pf1.
replace ((Pi_1p
       ∘ pProd_morph_ex (RCat_HP A (nthProdC rc A 1))
           (bullet
            ∘ pProd_morph_ex (RCat_HP A (nthProdC rc A 1)) Pi_1p (Pi_1p ∘ Pi_2p))
           (pt_morph (RCat_HP A (RCat_HP A RCat_term))))) with (bullet
            ∘ pProd_morph_ex (RCat_HP A (nthProdC rc A 1)) Pi_1p (Pi_1p ∘ Pi_2p)) in pf1.
simpl in pf1. rewrite assoc in pf1. rewrite ProdMapComp in pf1.
replace (Pi_1p
           ∘ pProd_morph_ex (RCat_HP A RCat_term)
               (proj1_sig p ∘ pt_morph (RCat_HP A RCat_term)) id) with (proj1_sig p ∘ pt_morph (RCat_HP A RCat_term)) in pf1.


replace (bullet_n A 0 bullet) with (bullet ∘(@Pi_1p _ _ _ A A (RCat_HP A A) A (id A) (id A)) ∘Pi_1p) . unfold bullet_n. simpl.
rewrite pProd_morph_com_1 in pf1.
Check (bullet_n A 0 bullet).
Check (Pi_1p ∘ bulletn_once A 0 bullet).

 with (bullet_n A 0 bullet) in pf1.
replace (pt_morph A) with ((pt_morph _) ∘ Pi_1p).
Check (@pProd_morph_ex  CRC rc CRC A RCat_term (RCat_HP A RCat_term) RCat_term (proj1_sig p) (pt_morph RCat_term) ) .

replace (@pProd_morph_ex  CRC rc CRC A RCat_term (@RCat_HP CRC rc CRC CRC A (@RCat_term CRC rc CRC CRC)) (@RCat_term CRC rc CRC CRC) (proj1_sig p) (pt_morph (@RCat_term CRC rc CRC CRC)) )  with
    ((@pProd_morph_ex  CRC rc CRC A (@RCat_term CRC rc CRC CRC) (@RCat_HP CRC rc CRC CRC A (@RCat_term CRC rc CRC CRC)) (@RCat_HP CRC rc CRC CRC A RCat_term)
          (proj1_sig p ∘ pt_morph (@RCat_HP CRC rc CRC CRC A (@RCat_term CRC rc CRC CRC)))  ((@Pi_2p CRC rc CRC A (@RCat_term CRC rc CRC CRC) (@RCat_HP CRC rc CRC CRC A (@RCat_term CRC rc CRC CRC))) ∘ id))∘ 
      (@pProd_morph_ex  CRC rc CRC A (@RCat_term CRC rc CRC CRC) (@RCat_HP CRC rc CRC CRC A (@RCat_term CRC rc CRC CRC)) RCat_term (proj1_sig p) ( pt_morph _) ) ).
replace (bullet_n A 1 bullet) with  (Pi_1p ∘ (bulletn_once  A 0 bullet)).
replace (bullet_n A 0 bullet) with (bullet ∘(pProd_morph_ex  A (id A) (id A)) 
    ∘ (@Pi_1p _ _ _ A RCat_term (RCat_HP A RCat_term))). simpl.
 rewrite ProdMapComp . rewrite id_unit_left.
rewrite assoc. rewrite assoc. rewrite ProdMapComp. 
replace (Pi_1p ∘ pProd_morph_ex RCat_term (proj1_sig p) (pt_morph RCat_term)) with
    (proj1_sig p).
replace (bullet_n A 1 bullet) with (Pi_1p ∘ (bulletn_once  A 0 bullet)) in pf1.

simpl. *)
Admitted.

(* axiom for products in compA - A^n X A^m = A^(n+m) *)
Definition AnAm_Anm `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) (a b : (all_prod_maps_Rcat _ _ _ _ A)) : Prop. 
destruct a as [a ap]; destruct b as [b bp]. unfold ObjCompAProp in ap; unfold ObjCompAProp in bp.
exact (∃ n m : nat, (a = nthProdC rc A n) /\ (b = nthProdC rc A m) /\ (@p_prod _ _ _  a b (RCat_HP a b) = nthProdC rc A (n + m))).
Defined.

Axiom AnAm_Anm_pf : forall `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) (a b : (all_prod_maps_Rcat _ _ _ _ A)),
AnAm_Anm _ _ _ _ A a b.

(* define partial products - isomorphic to those in underlying category but defined by 
adding the powers of A together *)
Definition CompAprod `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), (all_prod_maps_Rcat _ _ _ _ A).
intros a b. 
generalize (AnAm_Anm_pf _ _ _ _ A a b). intro AnAm_Anm_pf_ab.
destruct a as [a ap]; destruct b as [b bp]. unfold ObjCompAProp in ap; unfold ObjCompAProp in bp.
exists (RCat_HP a b). unfold ObjCompAProp. destruct ap as [an ap].
destruct bp as [bn bp]. 
unfold AnAm_Anm in AnAm_Anm_pf_ab. destruct AnAm_Anm_pf_ab as [n AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [m AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [AnAm_Anm_pf_a AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [AnAm_Anm_pf_b AnAm_Anm_pf_ab].
exists (n+m). auto.
 Defined.

Definition Pi_1pComA `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) :
forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), Hom ( CompAprod _ _ _ _ A a b) a.
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl.
exists Pi_1p. auto.
Defined.


Definition Pi_2pComA `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) :
forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), Hom ( CompAprod _ _ _ _ A a b) b.
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl.
exists Pi_2p. auto.
Defined.


Definition Pi_1TotComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), 
(rcCompAtype CRC rco CRC CRC _)  _ _ (Pi_1pComA _ _ _ _ A a b) = id ( CompAprod _ _ _ _ A a b).
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. (*
destruct RC. destruct RCat_RC. destruct (RCat_HP a b). simpl in Pi_1Tot. simpl.
destruct rco. simpl in Pi_1Tot.
rewrite Pi_1Tot.*)
apply pf_ir.
Defined.

Definition Pi_2TotComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), 
(rcCompAtype CRC rco CRC CRC _)  _ _ (Pi_2pComA _ _ _ _ A a b) = id ( CompAprod _ _ _ _ A a b).
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. (*
destruct RC. destruct RCat_RC. destruct (RCat_HP a b). simpl in Pi_1Tot. simpl.
destruct rco. simpl in Pi_1Tot.
rewrite Pi_1Tot.*)
apply pf_ir.
Defined.


Definition pProd_morph_ex_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
Hom p ( CompAprod _ _ _ _ A a b) .
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct p as [p pf]. destruct pf as [pn pf]. simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. 
exists (@pProd_morph_ex _ _ _ a b (RCat_HP a b) p r1 r2). auto.
Defined.

Definition pProd_morph_rest_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 ((rcCompAtype CRC rco CRC CRC _)  _ _ r1)∘((rcCompAtype CRC rco CRC CRC _)  _ _  r2) = 
      (rcCompAtype CRC rco CRC CRC _)  _ _  (pProd_morph_ex_ComA _ _ _ _ _ _ _ p r1 r2) . 
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct p as [p pf]. destruct pf as [pn pf]. simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. 
apply pf_ir.
Defined.

Definition pProd_morph_com_1_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Pi_1pComA _ _ _ _ A a b) ∘ (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2))  r1.
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct p as [p pf]. destruct pf as [pn pf]. simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. 
apply pf_ir.
Defined.

Definition pProd_morph_com_2_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Pi_2pComA _ _ _ _ A a b) ∘ (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2))  r2.
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct p as [p pf]. destruct pf as [pn pf]. simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. 
apply pf_ir.
Defined.

Definition pProd_morph_unique_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b) (pm : Hom p ( CompAprod _ _ _ _ A a b)), 
   (lt_eq _ _ ((Pi_1pComA _ _ _ _ A a b) ∘ pm)  r1) -> (lt_eq _ _ ((Pi_2pComA _ _ _ _ A a b) ∘ pm)  r2) 
        -> (((rcCompAtype CRC rco CRC CRC _)  _ _  r1)∘((rcCompAtype CRC rco CRC CRC _)  _ _  r2)
             = ((rcCompAtype CRC rco CRC CRC _)  _ _  pm)) -> pm = (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2).
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct p as [p pf]. destruct pf as [pn pf]. simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. destruct pm as [pm t3]. simpl in pm.
apply pf_ir.
Defined.


Definition CompA_Prods `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
  `{CRC : @CartRestrictionCat C rco RC} (A : CRC) : ∀ (a b : (all_prod_maps_Rcat _ _ _ _ A)) , ParProd a b.
intros a b . 
exists ( CompAprod _ _ _ _ A a b) (Pi_1pComA _ _ _ _ A a b) (Pi_2pComA _ _ _ _ A a b) (pProd_morph_ex_ComA _ _ _ _ A a b ).
exact (Pi_1TotComA _ _ _ _ _ a b). exact (Pi_2TotComA _ _ _ _ _ a b).
exact (pProd_morph_rest_ComA _ _ _ _ _ a b). 
exact (pProd_morph_com_1_ComA _ _ _ _ _ a b).
exact (pProd_morph_com_2_ComA _ _ _ _ _ a b).
exact (pProd_morph_unique_ComA _ _ _ _ _ a b).
Defined.

(* define partial terminal objects *)
Definition CompAterm `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) :  (all_prod_maps_Rcat _ _ _ _ A).
exists (nthProdC rc A 0). unfold ObjCompAProp. simpl. exists 0. simpl. auto. 
Defined.

Definition CompApt_morph `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) :  forall (a : (all_prod_maps_Rcat _ _ _ _ A)),
  Hom a (CompAterm _ _ _ _ A).
intro. destruct a as [a a_n]. unfold ObjCompAProp in a_n. 
destruct a_n as [a_n]. simpl. exists (pt_morph a). auto.
Defined.

 
Definition CompAm_t `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  forall (a : (all_prod_maps_Rcat _ _ _ _ A)),
  (rcCompAtype CRC rco CRC CRC _)  _ _   (CompApt_morph _ _ _ _ A a) = id a.
intro. destruct a as [a a_n]. unfold ObjCompAProp in a_n. 
destruct a_n as [a_n]. simpl.
apply pf_ir.
Defined.

Definition CompAid_ptm `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  
  id (CompAterm _ _ _ _ A) = CompApt_morph _ _ _ _ A (CompAterm _ _ _ _ A) .
simpl.
apply pf_ir.
Defined.

Definition CompAunique_g `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  forall (a b : (all_prod_maps_Rcat _ _ _ _ A)) (f : Hom a b),
((CompApt_morph _ _ _ _ A b) ∘ f) = (CompApt_morph _ _ _ _ A a) ∘ ((rcCompAtype CRC rco CRC CRC _)  _ _ f).
intros. destruct a as [a a_n]. destruct b as [b b_n]. unfold ObjCompAProp in a_n. 
unfold ObjCompAProp in b_n. destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
apply pf_ir.
Defined.

Definition CompA_Term `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
  `{CRC : @CartRestrictionCat C rco RC} (A : CRC) : 
@ParTerm (all_prod_maps_Rcat _ _ _ _ A) (rcCompA _ _ _ _ A) (all_prod_maps_Rcat _ _ _ _ A) .
exists (CompAterm _ _ _ _ A) (CompApt_morph _ _ _ _ A ).
exact (CompAm_t _ _ _ _ A ).
exact (CompAid_ptm _ _ _ _ A ).
exact (CompAunique_g _ _ _ _ A ).
Defined.



Definition CompA_CRCat `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} `{A : C} {CRC : @CartRestrictionCat C rco RC}  :
  CartRestrictionCat  (rcCompA _ _ _ _ A).
exists. exact (CompA_Term  A). exact (CompA_Prods A).
Defined.

(*
Definition CompA_CRCat `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} `(A : C):
  forall (CRC : @CartRestrictionCat C rco RC)  ,
@CartRestrictionCat (all_prod_maps_Rcat _ _ _ _ A) (rcCompA _ _ _ _ A) (all_prod_maps_Rcat _ _ _ _ A) .
  exists. exact (CompA_Term  A). exact (CompA_Prods A).
Defined. *)


Class CompACat `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) : Type :=
{
  comp_cat : CartRestrictionCat (rcCompA _ _ _ _ A) := CompA_CRCat    ;
  is_comb_complete : exists (bullet : Hom (RCat_HP A A) A), (TxyUniv A A A (RCat_HP A A) bullet)
}.


Coercion comp_cat : CompACat >-> CartRestrictionCat.

(*
Instance RestrictionCatsAreCategories `{ RC: RestrictionCat  }  : Category := C.

Coercion RestrictionCatsAreCategories : RestrictionCat >-> Category. *)