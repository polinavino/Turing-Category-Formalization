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
Require Import Par_Cat.
Require Import Main_Func.
Require Import NatTrans Func_Cat Operations.


Generalizable All Variables. 


(* define a category all_prod_maps_cat as a full subcategory of the underlying CRC 
with objects 1, A, A^n, ... *)

Instance all_prod_maps_cat (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : 
Category := Full_SubCategory C (fun (x : CRC) => (exists (n : nat), x = (nthProdC rco A n))).


(* objects in CRC that are A^n are equal *)
Definition same_n_obj (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_cat C rco RC CRC A)) : Prop.
destruct a as [a ap]; destruct b as [b bp]. 
exact ((∃ n : nat, (a = nthProdC rco A n) /\ (b = nthProdC rco A n )) -> (a = b)) . 
Defined.

Definition same_n_obj_pf (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_cat C rco RC CRC A)) : 
same_n_obj CRC rco CRC CRC A a b. 
unfold same_n_obj. 
destruct a as [a ap]; destruct b as [b bp]. 
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




Definition rcCompA  (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC)  (A : CRC) :  RestrictionComb (all_prod_maps_cat C rco RC CRC A).
exists (@rcCompAtype  C rco RC CRC A); intros; destruct a as [a]; try (destruct b as [b]);
try (destruct c as [c]); destruct f as [f]; try (destruct g as [g]); unfold  rcCompAtype; simpl.
(*destruct C; destruct RC; destruct CRC; destruct rco; simpl; apply pf_ir *)
rewrite (@rc1 C rco). auto.
rewrite (@rc2 C rco). auto.
rewrite (@rc3 C rco). auto.
rewrite (@rc4 C rco). auto.
Defined.


Instance all_prod_maps_Rcat (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) :
RestrictionCat (all_prod_maps_cat _ _ _ _ A) (rcCompA _ _ _ _ A).
exists. Defined.


Definition A1toAtype (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) := (Hom (nthProdC rco A 1) A).

Definition AtoAtype(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) := (Hom A A).

Definition A1toAmap (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : A1toAtype _ _ _ _ A -> AtoAtype _ _ _ _  A.
intro f. simpl in f. exact (compose _ _ _ _ (@pProd_morph_ex CRC rco CRC _ _ _ _ (id A) (pt_morph _))  f).
Defined.

Definition AtoA1map (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : AtoAtype _ _ _ _ A -> A1toAtype _ _ _ _ A.
intro f. simpl in f. exact (compose _ _ _ _ Pi_1p  f).
Defined.

(*
Coercion AtoA1map : AtoAtype >-> A1toAtype.
*)

Definition A1toA1type (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) := (Hom (nthProdC rco A 1) (nthProdC rco A 1)).

Definition A1toA1map (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : A1toA1type _ _ _ _ A -> AtoAtype _ _ _ _ A.
intro f. unfold A1toA1type in f. unfold AtoAtype. 
exact (compose _ _ _ _  (@pProd_morph_ex CRC rco CRC _ _ _ _ (id A) (pt_morph _)) (compose _ _ _ _ f Pi_1p ) )    .
Defined.

(* Coercion A1toA1map : A1toA1type >-> AtoAtype. *)

Definition AtoAmap (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC): AtoAtype  _ _ _ _ A ->  A1toA1type _ _ _ _ A.
intro f. unfold AtoAtype in f. unfold A1toA1type . 
exact (compose _ _ _ _ (compose _ _ _ _ Pi_1p f) (@pProd_morph_ex CRC rco CRC _ _ _ _ (id A) (pt_morph _))  )    .
Defined.

(* Coercion AtoAmap : AtoAtype  >-> A1toA1type. *)


Definition A11toA1map (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : A1toA1type _ _ _ _ A ->  A1toAtype _ _ _ _ A.
intro f. unfold A1toA1type in f. unfold A1toAtype . 
exact  (compose _ _ _ _ f Pi_1p )     .
Defined.

(* Coercion A11toA1map : A1toA1type  >-> A1toAtype. *)

(*  id A is computable implies id A^m is computable *)
Definition idm_comp (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (bullet : Hom (RCat_HP A A) A) 
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
Definition AnAm_Anm (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_Rcat _ _ _ _ A)) : Prop. 
destruct a as [a ap]; destruct b as [b bp]. 
exact (∃ n m : nat, (a = nthProdC rco A n) /\ (b = nthProdC rco A m) /\ (@p_prod _ _ _  a b (RCat_HP a b) = nthProdC rco A (n + m))).
Defined.

Axiom AnAm_Anm_pf : forall (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) (a b : (all_prod_maps_Rcat _ _ _ _ A)),
AnAm_Anm _ _ _ _ A a b.

(* define partial products - isomorphic to those in underlying category but defined by 
adding the powers of A together *)
Definition CompAprod (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), (all_prod_maps_Rcat _ _ _ _ A).
intros a b. 
generalize (AnAm_Anm_pf _ _ _ _ A a b). intro AnAm_Anm_pf_ab.
destruct a as [a ap]; destruct b as [b bp]. 
exists (RCat_HP a b). destruct ap as [an ap].
destruct bp as [bn bp]. 
unfold AnAm_Anm in AnAm_Anm_pf_ab. destruct AnAm_Anm_pf_ab as [n AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [m AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [AnAm_Anm_pf_a AnAm_Anm_pf_ab].
destruct AnAm_Anm_pf_ab as [AnAm_Anm_pf_b AnAm_Anm_pf_ab].
exists (n+m). auto.
 Defined.


Definition Pi_1pComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) :
forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), Hom ( CompAprod _ _ _ _ A a b) a.
intros. destruct a as [a a_n]. destruct b as [b b_n].  simpl.
exists Pi_1p. auto.
Defined.


Definition Pi_2pComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) :
forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), Hom ( CompAprod _ _ _ _ A a b) b.
intros. destruct a as [a a_n]. destruct b as [b b_n]. 
simpl. exists Pi_2p. auto.
Defined.



Definition Pi_1TotComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), 
(rcCompAtype CRC rco CRC CRC _)  _ _ (Pi_1pComA _ _ _ _ A a b) = id ( CompAprod _ _ _ _ A a b).
intros. destruct a as [a a_n]. destruct b as [b b_n].
 destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
rewrite (@Pi_1Tot _ _ _ a b (RCat_HP a b) ). auto.
Defined.


Definition Pi_2TotComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b : (all_prod_maps_Rcat _ _ _ _ A)), 
(rcCompAtype CRC rco CRC CRC _)  _ _ (Pi_2pComA _ _ _ _ A a b) = id ( CompAprod _ _ _ _ A a b).
intros. destruct a as [a a_n]. destruct b as [b b_n]. 
destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
rewrite (@Pi_2Tot _ _ _ a b (RCat_HP a b) ). auto.
Defined.



Definition pProd_morph_ex_ComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
Hom p ( CompAprod _ _ _ _ A a b) .
intros. destruct a as [a a_n]. destruct b as [b b_n]. 
simpl. 
destruct p as [p pf].  simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl. 
exists (@pProd_morph_ex _ _ _ a b (RCat_HP a b) p r1 r2). auto.
Defined.


Definition pProd_morph_rest_ComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 ((rcCompAtype CRC rco CRC CRC _)  _ _ r1)∘((rcCompAtype CRC rco CRC CRC _)  _ _  r2) = 
      (rcCompAtype CRC rco CRC CRC _)  _ _  (pProd_morph_ex_ComA _ _ _ _ _ _ _ p r1 r2) . 
intros. destruct a as [a a_n]. destruct b as [b b_n].
simpl. 
destruct p as [p pf].  simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl.  
rewrite (@pProd_morph_rest C rco _ _ _(RCat_HP a b)).
auto. Defined.


Definition pProd_morph_com_1_ComA (C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) 
  (CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Pi_1pComA _ _ _ _ A a b) ∘ (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2))  r1.
intros. destruct a as [a a_n]. destruct b as [b b_n].
simpl. 
destruct p as [p pf].  simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl.  
generalize (@pProd_morph_com_1 C rco RC a b (RCat_HP a b) p r1 r2). 
unfold lt_eq. simpl. destruct RC. simpl. destruct C.
simpl. intro H. rewrite H.
auto. Defined.


Definition pProd_morph_com_2_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Pi_2pComA _ _ _ _ A a b) ∘ (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2))  r2.
intros. destruct a as [a a_n]. destruct b as [b b_n].
simpl. 
destruct p as [p pf].  simpl in r1. destruct r1 as [r1 t].
simpl in r2. destruct r2 as [r2 t2]. simpl.  
generalize (@pProd_morph_com_2 C rco RC a b (RCat_HP a b) p r1 r2). 
unfold lt_eq. simpl. destruct RC. simpl. destruct C.
simpl. intro H. rewrite H.
auto. Defined.

Definition pProd_morph_unique_ComA `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : forall (a b p : (all_prod_maps_Rcat _ _ _ _ A))
(r1 : Hom p a) (r2 : Hom p b) (pm : Hom p ( CompAprod _ _ _ _ A a b)), 
   (lt_eq _ _ ((Pi_1pComA _ _ _ _ A a b) ∘ pm)  r1) -> (lt_eq _ _ ((Pi_2pComA _ _ _ _ A a b) ∘ pm)  r2) 
        -> (((rcCompAtype CRC rco CRC CRC _)  _ _  r1)∘((rcCompAtype CRC rco CRC CRC _)  _ _  r2)
             = ((rcCompAtype CRC rco CRC CRC _)  _ _  pm)) -> pm = (pProd_morph_ex_ComA _ _ _ _ A a b p r1 r2).
intros a b p r1 r2 pm h1 h2 h3. destruct a as [a a_n]. destruct b as [b b_n].
simpl. 
destruct p as [p pf].  simpl in r1. destruct r1 as [r1 t].
destruct pm as [pm pm_t]. simpl in pm.
simpl in r2. destruct r2 as [r2 t2]. simpl.
simpl in h1; simpl in h2; simpl in h3.  
generalize (@pProd_morph_unique C rco RC a b (RCat_HP a b) p r1 r2 pm). 
unfold lt_eq. simpl. destruct RC. simpl. destruct C.
simpl. intro Hh . inversion h1. inversion h2. inversion h3.
 rewrite (Hh H0 H1 H2). 
auto. Defined.



Definition CompA_Prods `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : ∀ (a b : (all_prod_maps_Rcat _ _ _ _ A)) , ParProd a b.
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
exists (nthProdC rc A 0).  simpl. exists 0. simpl. auto. 
Defined.

Definition CompApt_morph `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(CRC : @CartRestrictionCat C rc RC) (A : CRC) :  forall (a : (all_prod_maps_Rcat _ _ _ _ A)),
  Hom a (CompAterm _ _ _ _ A).
intro. destruct a as [a a_n].  
simpl. exists (pt_morph a). auto.
Defined.

 
Definition CompAm_t `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  forall (a : (all_prod_maps_Rcat _ _ _ _ A)),
  (rcCompAtype CRC rco CRC CRC _)  _ _   (CompApt_morph _ _ _ _ A a) = id a.
intro. destruct a as [a a_n]. 
destruct a_n as [a_n]. simpl.
rewrite (@morph_total _ _ RC RCat_term a).
auto. Defined.


Definition CompAid_ptm `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  
  id (CompAterm _ _ _ _ A) = CompApt_morph _ _ _ _ A (CompAterm _ _ _ _ A) .
simpl.
rewrite (@id_is_ptm _ _ RC RCat_term ).
auto. Defined.

Definition CompAunique_g `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  forall (a b : (all_prod_maps_Rcat _ _ _ _ A)) (f : Hom a b),
((CompApt_morph _ _ _ _ A b) ∘ f) = (CompApt_morph _ _ _ _ A a) ∘ ((rcCompAtype CRC rco CRC CRC _)  _ _ f).
intros. destruct a as [a a_n]. destruct b as [b b_n]. 
destruct a_n as [a_n]. destruct b_n as [b_n]. simpl. 
destruct f as [f fn].
rewrite (@pt_morph_unique_greatest _ _ RC RCat_term a b f ).
auto. Defined.


Definition CompA_Term `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) : 
@ParTerm (all_prod_maps_Rcat C rco RC CRC A) (rcCompA C rco RC CRC A) (all_prod_maps_Rcat C rco RC CRC A).
exists (CompAterm C rco RC CRC A) (CompApt_morph C rco RC CRC A ).
exact (CompAm_t C rco RC CRC A ).
exact (CompAid_ptm C rco RC CRC A ).
exact (CompAunique_g C rco RC CRC A ).
Defined.


Instance CompA_CRCat `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) :  
@CartRestrictionCat  (all_prod_maps_Rcat C rco RC CRC A) (rcCompA C rco RC CRC  A) (all_prod_maps_Rcat C rco RC CRC A).
exists. exact (CompA_Term C rco RC CRC A). exact (CompA_Prods C rco RC CRC A).
Defined.

Definition idem_class `(C : Category) := forall (a : C) (e : Hom a a)  , Prop .

Definition split_obj `(C : Category) (E : idem_class C) := { a : C & {e : Hom a a | ((E a e) /\ (  e ∘ e = e )) } } .

Definition split_hom `(C : Category) (E : idem_class C) 
    := fun ( ce df : split_obj C E) => { f_ef : Hom (projT1 ce) (projT1 df) 
      | (proj1_sig (projT2 df)) ∘ f_ef = f_ef /\ f_ef = f_ef ∘ (proj1_sig (projT2 ce)) }.

Definition split_comp `(C : Category) (E : idem_class C) : forall ( ce df gh : split_obj C E) , 
    (split_hom C E ce df) ->  (split_hom C E df gh) ->  (split_hom C E ce gh).
unfold split_hom. intros ce df gh f_ef g_ef. 
destruct ce as [a [cf [pfce pfcei] ] ] ; destruct df as [b [df [pfdf pfdfi] ] ]
; destruct gh as [c [gh [pfgh pfghi] ] ]. simpl.
simpl in f_ef; simpl in g_ef. destruct f_ef as [f_ef [fef1 fef2]].
destruct g_ef as [g_ef [gef1 gef2]]. exists (g_ef ∘ f_ef).
split. rewrite <- assoc. rewrite gef1. auto.
rewrite assoc. rewrite <- fef2. auto.
Defined.

Definition split_id `(C : Category) (E : idem_class C) : forall ( ce : split_obj C E) , 
    (split_hom C E ce ce).
unfold split_hom. destruct ce as [a [cf [pfce pfcei] ] ].
simpl. exists cf. auto. Defined.

Definition  split_assoc `(C : Category) (E : idem_class C) : ∀ {a b c d : split_obj C E} (f : (split_hom C E a b))
 (g : (split_hom C E b c)) (h : (split_hom C E c d)),
            (split_comp _ _ _ _ _ f (split_comp _ _ _ _ _  g h) ) = (split_comp _ _ _ _ _  (split_comp _ _ _ _ _ f g) h).
Admitted.

Definition  split_assoc_sym `(C : Category) (E : idem_class C) : ∀ {a b c d : split_obj C E} (f : (split_hom C E a b))
 (g : (split_hom C E b c)) (h : (split_hom C E c d)),
            (split_comp _ _ _ _ _  (split_comp _ _ _ _ _ f g) h) = (split_comp _ _ _ _ _ f (split_comp _ _ _ _ _  g h) ).
Admitted.

Definition split_id_unit_left `(C : Category) (E : idem_class C) : ∀ {a b  : split_obj C E} (h : (split_hom C E a b)),
            (split_comp _ _ _ _ _  h (split_id C E b)) = h.
Admitted.

Definition split_id_unit_right `(C : Category) (E : idem_class C) : ∀ {a b  : split_obj C E} (h : (split_hom C E a b)),
            (split_comp _ _ _ _ _  (split_id C E a) h) = h.
Admitted.


(* define SplitC as a restriction category *)
Definition SplitC `(C : Category) (E : idem_class C) : Category.
exists (split_obj C E) (split_hom C E) (split_comp C E) (split_id C E).
exact (@split_assoc _ _).
exact (@split_assoc_sym _ _).
exact (@split_id_unit_left _ _).
exact (@split_id_unit_right _ _).
Defined.

Definition SplitRCtype `(C : Category) (E : idem_class C) 
(rco : @RestrictionComb C) (RC : @RestrictionCat C rco) : @rcType (SplitC C E).
unfold rcType. intros ce df. 
destruct ce as [a [cf [pfce pfcei] ] ] ; destruct df as [b [df [pfdf pfdfi] ] ].
simpl. unfold split_hom.
intro f_ef. destruct f_ef as [f_ef [fef1 fef2]]. simpl.
simpl in f_ef; simpl in fef1; simpl in fef2.
exists ((@rc RC rco a b (df ∘ f_ef ∘ cf) ) ∘ cf). split.
destruct rco. simpl. rewrite <- assoc.
rewrite <- assoc. rewrite fef1. rewrite <- rc4.
rewrite <- fef2. rewrite assoc.
rewrite pfcei. auto. rewrite <- assoc.
rewrite fef1. rewrite assoc. rewrite pfcei.
auto. Defined. 


Definition sp_rc1  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(E : idem_class C) : ∀ (a b : split_obj C E) 
(f : split_hom C E a b),
split_comp C E a a b (SplitRCtype C E rco RC a b f) f = f .
Admitted.

Definition sp_rc2  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
 : forall (a b c : C)  (gh : Hom c c) ( g_ef : Hom _ _)
( cf : Hom a a) ( df : Hom b b) (f_ef : Hom a b),  (rc a c (gh ∘ g_ef ∘ cf) ∘ cf) ∘ rc a b (df ∘ f_ef ∘ cf) ∘ cf =
(rc a b (df ∘ f_ef ∘ cf) ∘ cf) ∘ rc a c (gh ∘ g_ef ∘ cf) ∘ cf.
Admitted.


Definition sp_rc4  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
 : forall (a b c : C)  (gh : Hom c c) ( g_ef : Hom _ _)
( cf : Hom a a) ( df : Hom b b) (f_ef : Hom a b), (rc b c (gh ∘ g_ef ∘ df) ∘ df) ∘ f_ef =
f_ef ∘ rc a c (gh ∘ (g_ef ∘ f_ef) ∘ cf) ∘ cf .
Admitted.

Definition Split_rc  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(E : idem_class C) :  RestrictionComb (SplitC C E).
exists (SplitRCtype C E rco RC); unfold split_hom;
try (intros ce df gh f_ef g_ef) ;
try (destruct ce as [a [cf [pfce pfcei] ] ]) ; try (destruct df as [b [df [pfdf pfdfi] ] ] )
; try (destruct gh as [c [gh [pfgh pfghi] ] ] ) ;
try ( destruct f_ef as [f_ef [fef1 fef2]] ) ;
try ( destruct g_ef as [g_ef [gef1 gef2]] ) ;
try (simpl in f_ef; simpl in g_ef); simpl ;
try (simpl in gef1; simpl in gef2; simpl in fef1; simpl in fef2);
 try (apply exist_eq ; simpl) ; 
try (apply sp_rc1 ); try (rewrite  (sp_rc2 _ _ _ a b c gh g_ef cf df f_ef )); 
try (apply (sp_rc4 _ _ _ a b c gh g_ef cf df f_ef )) ;
destruct rco; simpl. auto. 
rewrite <- assoc. rewrite <- assoc. rewrite gef1. rewrite <- assoc.
rewrite <- gef2. rewrite gef1. rewrite <-  fef2.
rewrite assoc. rewrite assoc. rewrite fef1.
rewrite pfcei. rewrite <- assoc. rewrite <- assoc.
rewrite (rc4 _ _ _ cf ((g_ef ∘ rc a b f_ef) ∘ cf)). 
rewrite assoc. rewrite assoc. rewrite pfcei.
rewrite <- assoc. 
rewrite <- (rc4 _ _ _ cf (g_ef ∘ rc a b f_ef)).
rewrite rc3. rewrite rc2. 
replace ((rc a b f_ef ∘ cf) ∘ rc a c g_ef)  with (rc a b f_ef ∘ (cf ∘ rc a c g_ef)).
replace (cf ∘ rc a c g_ef) with ( rc a c g_ef ∘ cf). rewrite assoc.
rewrite assoc. rewrite assoc. rewrite pfcei. auto. 
rewrite rc4. rewrite <- gef2. auto.
rewrite assoc. auto.
Defined.

(* instantiate SplitC as a restriction category *)
Instance SplitRC `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(E : idem_class C) :  RestrictionCat (SplitC C E) (Split_rc C rco RC E).
exists. Defined.

(* class of idempotents closed under taking products Prop *)
Definition E_closed_prod `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) := forall (a b : SplitRC C rco RC E),
E (RCat_HP (projT1 a) (projT1 b)) (pProd_morph_ex _ ((proj1_sig (projT2 a)) ∘ Pi_1p) ((proj1_sig (projT2 b)) ∘ Pi_2p)).

Definition prod_map_idem `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) : forall a b, forall (ea : Hom a a), forall (eb : Hom b b),
ea ∘ ea = ea -> eb ∘ eb = eb ->
 (@pProd_morph_ex _ _ _ a b (RCat_HP a b) (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) )) ) =
(@pProd_morph_ex _ _ _ a b (RCat_HP a b) (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) )))
∘ (@pProd_morph_ex _ _ _ a b (RCat_HP a b) (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) ))).
intros. rewrite (ProdMapComp CRC). 
rewrite assoc. rewrite assoc.
generalize (@pProd_morph_com_2 RC rco CRC a b (RCat_HP a b) (RCat_HP a b) (ea ∘ Pi_1p) (eb ∘ Pi_2p)).
generalize (@pProd_morph_com_1 RC rco CRC a b (RCat_HP a b) (RCat_HP a b) (ea ∘ Pi_1p) (eb ∘ Pi_2p)).
unfold lt_eq. destruct RC. intros. destruct C.
replace RCat_RC with rco in rc_d.
destruct rco. simpl in H1. simpl. simpl in H2.
rewrite <- H1. rewrite <- H2. 
rewrite rc_d. simpl. rewrite (@Pi_1Tot _ _ _ a b (RCat_HP a b)). simpl.
rewrite id_unit_left. rewrite rc_d. simpl.
 rewrite (@Pi_2Tot _ _ _ a b (RCat_HP a b)). simpl. 
rewrite id_unit_left. rewrite <- assoc. rewrite <- assoc.
compute in H. rewrite H. rewrite <- assoc. rewrite <- assoc.
compute in H0. rewrite H0.
rewrite <- (ProdMapComp CRC).
rewrite rc1. auto. auto.
Defined.

Definition Split_prod  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
  forall (a b : SplitRC C rco RC E), SplitRC C rco RC E.
unfold SplitRC. simpl. unfold split_obj. intros a b.
unfold E_closed_prod in pfe_cl. simpl in pfe_cl.
generalize (pfe_cl a b); intros pf.
destruct a as [a [ea pa2]]. destruct b as [b [eb pb2]].
exists (RCat_HP a b). 
exists (pProd_morph_ex _ (ea ∘ Pi_1p ) (eb ∘ Pi_2p )).
simpl in pf. split. exact pf.
generalize (ProdMapComp CRC a b (RCat_HP a b) (RCat_HP a b) (RCat_HP a b)).
 intro ProdMapComp. rewrite ProdMapComp. rewrite assoc. 
generalize (@pProd_morph_com_2 RC rco CRC a b (RCat_HP a b) (RCat_HP a b) (ea ∘ Pi_1p) (eb ∘ Pi_2p)).
generalize (@pProd_morph_com_1 RC rco CRC a b (RCat_HP a b) (RCat_HP a b) (ea ∘ Pi_1p) (eb ∘ Pi_2p)).
unfold lt_eq. destruct RC. intros pmc1 pmc2.  destruct C. 
destruct (RCat_HP a b) as [aXb]. simpl.
simpl in pmc2. simpl in pmc1. rewrite assoc.  rewrite <- pmc2.
rewrite assoc. rewrite <- pmc1. 
replace RCat_RC with rco in rc_d.
simpl in rc_d. rewrite rc_d.  simpl in Pi_1Tot.
rewrite Pi_1Tot. rewrite id_unit_left.
rewrite rc_d. simpl in Pi_2Tot. rewrite Pi_2Tot.
rewrite id_unit_left.
simpl in pProd_morph_rest. rewrite <- pProd_morph_rest.
rewrite <- (assoc _ _ _ _ _ _ eb  ).
destruct pb2 as [pbb pbbb]. simpl in pbbb. rewrite pbbb.
rewrite <- (assoc _ _ _ _ _ _ ea  ). rewrite <- (assoc _ _ _ _ _ _ ea  ).
destruct pa2 as [paa paaa]. simpl in paaa. rewrite paaa.
rewrite (assoc _ _ _ _ _ _ ea  ). simpl in ProdMapComp.
rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
 rewrite <- ProdMapComp. rewrite <- ProdMapComp.
rewrite assoc. rewrite pProd_morph_rest. 
destruct rco. simpl. simpl in rc1.
rewrite rc1. auto. auto.
Defined.
 


Definition Split_Pi_1p  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b : (SplitRC C rco RC E)), Hom ( Split_prod C rco RC CRC E pfe_cl a b) a.
 unfold SplitRC. simpl. unfold split_obj.
unfold split_hom. unfold E_closed_prod. intros a b.
generalize (pfe_cl a b). intro pfe_clab.
unfold E_closed_prod in pfe_clab. simpl in pfe_clab.
destruct a as [a [ea pa2]]. destruct b as [b [eb pb2]].
simpl. simpl in pfe_clab. exists (ea ∘ Pi_1p ∘ (rc (RCat_HP a b) (RCat_HP a b)
        (pProd_morph_ex (RCat_HP a b)
        (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) 
        (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) ) )))). split. destruct pa2 as [paa2 paaa2].
rewrite <- assoc. rewrite paaa2. auto. 
replace (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )
  ∘ rc (RCat_HP a b) 
      (RCat_HP a b)
      (pProd_morph_ex (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) )))) with
  ((@Pi_1p RC rco CRC _ _ (RCat_HP a b) )
∘ pProd_morph_ex (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) ))).
destruct pa2 as [pa pa2]. destruct pb2 as [pb pb2]. rewrite assoc.
generalize  (prod_map_idem _ rco RC CRC  a b  ea eb pa2 pb2) . intro. 
compute. compute in H. destruct CRC. destruct RCat_HP. destruct C.
rewrite <- H. auto.
compute. destruct CRC. destruct RCat_HP. destruct C. destruct RC.
unfold lt_eq in pProd_morph_com_1.
rewrite <- assoc. 
rewrite <- pProd_morph_com_1. replace RCat_RC with rco in rc_d.
destruct rco. simpl. simpl in rc_d.
rewrite rc_d. simpl in Pi_1Tot. rewrite Pi_1Tot. rewrite id_unit_left.
auto. auto.
Defined.


Definition Split_Pi_2p  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b : (SplitRC C rco RC E)), Hom ( Split_prod C rco RC CRC E pfe_cl a b) b.
 unfold SplitRC. simpl. unfold split_obj.
unfold split_hom. unfold E_closed_prod. intros a b.
generalize (pfe_cl a b). intro pfe_clab.
unfold E_closed_prod in pfe_clab. simpl in pfe_clab.
destruct a as [a [ea pa2]]. destruct b as [b [eb pb2]].
simpl. simpl in pfe_clab. exists (eb ∘ Pi_2p ∘ (rc (RCat_HP a b) (RCat_HP a b)
        (pProd_morph_ex (RCat_HP a b)
        (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) 
        (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) ) )))). split. destruct pb2 as [pbb2 pbbb2].
rewrite <- assoc. rewrite pbbb2. auto. 
replace (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) )
  ∘ rc (RCat_HP a b) 
      (RCat_HP a b)
      (pProd_morph_ex (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) )))) with
  ((@Pi_2p RC rco CRC _ _ (RCat_HP a b) )
∘ pProd_morph_ex (RCat_HP a b) (ea ∘ (@Pi_1p RC rco CRC _ _ (RCat_HP a b) )) (eb ∘ (@Pi_2p RC rco CRC _ _ (RCat_HP a b) ))).
destruct pa2 as [pa pa2]. destruct pb2 as [pb pb2]. rewrite assoc.
generalize  (prod_map_idem _ rco RC CRC  a b  ea eb pa2 pb2) . intro. 
compute. compute in H. destruct CRC. destruct RCat_HP. destruct C.
rewrite <- H. auto.
compute. destruct CRC. destruct RCat_HP. destruct C. destruct RC.
unfold lt_eq in pProd_morph_com_2.
rewrite <- assoc. 
rewrite <- pProd_morph_com_2. replace RCat_RC with rco in rc_d.
destruct rco. simpl. simpl in rc_d.
rewrite rc_d. simpl in Pi_2Tot. rewrite Pi_2Tot. rewrite id_unit_left.
auto. auto.
Defined.

Definition Split_Pi_1Tot  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : forall (a b : (SplitRC C rco RC E)), 
((SplitRCtype C E rco RC)  _  a (Split_Pi_1p CRC rco CRC CRC _ pfe_cl a b)) = id _.
Admitted.

Definition Split_Pi_2Tot  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b : (SplitRC C rco RC E)), 
((SplitRCtype C E rco RC)  _ b (Split_Pi_2p CRC rco CRC CRC E pfe_cl a b)) = id _.
Admitted.

Definition Split_pProd_morph_ex  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ): 
forall (a b p : (SplitRC C rco RC E))
(r1 : Hom p a) (r2 : Hom p b),
Hom p ( Split_prod CRC rco CRC CRC E pfe_cl a b)  .
 unfold SplitRC. simpl. unfold split_obj.
unfold split_hom. unfold E_closed_prod. intros a b.
generalize (pfe_cl a b). intro pfe_clab.
destruct a as [a [ea pa2]]. destruct b as [b [eb pb2]].
simpl. unfold E_closed_prod in pfe_clab. simpl in pfe_clab.
intro p. destruct p as [c [ec [ec1 ec2]]]. simpl.
intros f g. destruct f as [f [f1 f2]].
destruct g as [g [g1 g2]].
exists (pProd_morph_ex c f g). split.
rewrite <- f1. rewrite <- g1. 
generalize (fun (c d : CRC) => ProdMapComp CRC a b c d (RCat_HP a b) ). intro ProdMapComp.
rewrite (ProdMapComp ).
rewrite assoc. rewrite assoc.
destruct CRC. destruct RCat_HP. destruct C. destruct RC.
unfold lt_eq in pProd_morph_com_2.
simpl.
rewrite <- pProd_morph_com_2. 
unfold lt_eq in pProd_morph_com_1.
rewrite <- pProd_morph_com_1.
replace RCat_RC with rco in rc_d.
destruct rco. simpl. simpl in rc_d. rewrite rc_d.
simpl in Pi_1Tot. simpl in Pi_2Tot. 
rewrite Pi_1Tot. rewrite id_unit_left. rewrite rc_d.
rewrite Pi_2Tot. rewrite id_unit_left.
simpl in ProdMapComp. 
rewrite <- assoc. rewrite  <- assoc.
destruct pa2 as [pa2 paa2]. simpl in paa2. rewrite paa2.
rewrite <- assoc. rewrite  <- assoc.
destruct pb2 as [pb2 pbb2]. simpl in pbb2. rewrite pbb2.
rewrite <- ProdMapComp. rewrite <- rc1. simpl. auto.
auto.
rewrite (ProdMapComp CRC).
rewrite <- g2. rewrite <- f2. auto.
Defined.


Definition Split_pProd_morph_rest  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b p : (SplitRC C rco RC E))
(r1 : Hom p a) (r2 : Hom p b),
 ((SplitRCtype C E rco RC)  _ _ r1)∘((SplitRCtype C E rco RC)  _ _  r2) = 
      (SplitRCtype C E rco RC)  _ _  (Split_pProd_morph_ex  C rco RC CRC E pfe_cl _ _ p r1 r2) . 
Admitted.

Definition Split_pProd_morph_com_1  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b p : (SplitRC C rco RC E))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Split_Pi_1p C rco RC CRC E pfe_cl a b) ∘ (Split_pProd_morph_ex C rco RC CRC E pfe_cl a b p r1 r2))  r1.
Admitted.

Definition Split_pProd_morph_com_2  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC)(E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b p : (SplitRC C rco RC E))
(r1 : Hom p a) (r2 : Hom p b),
 lt_eq _ _ ((Split_Pi_2p C rco RC CRC E pfe_cl a b) ∘ (Split_pProd_morph_ex C rco RC CRC E pfe_cl a b p r1 r2))  r2.
Admitted.

Definition Split_pProd_morph_unique  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) : 
forall (a b p : (SplitRC C rco RC E))
(r1 : Hom p a) (r2 : Hom p b) (pm : Hom p ( Split_prod _ _ _ _ E pfe_cl a b)), 
   (lt_eq _ _ ((Split_Pi_1p C rco RC CRC E pfe_cl a b) ∘ pm)  r1) -> (lt_eq _ _ ((Split_Pi_2p C rco RC CRC E pfe_cl a b) ∘ pm)  r2) 
        -> (((SplitRCtype C E rco RC)  _ _  r1)∘((SplitRCtype C E rco RC)  _ _  r2)
             = ((SplitRCtype C E rco RC)  _ _  pm)) -> pm = (Split_pProd_morph_ex  C rco RC CRC E pfe_cl _ _ p r1 r2).
Admitted.

(* products in SplitRC *)
Definition Split_Prods  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E ) :  forall (a b : (SplitC C E)), 
@ParProd (SplitRC C rco CRC E) (Split_rc C rco CRC E ) (SplitRC C rco CRC E ) a b.
intros.
exists  (Split_prod CRC rco CRC CRC E pfe_cl a b) (Split_Pi_1p CRC rco CRC CRC E pfe_cl a b)
(Split_Pi_2p CRC rco CRC CRC E pfe_cl a b) (Split_pProd_morph_ex CRC rco CRC CRC E pfe_cl a b).
exact (Split_Pi_1Tot CRC rco CRC CRC E pfe_cl a b).
exact (Split_Pi_2Tot CRC rco CRC CRC E pfe_cl a b).
exact (Split_pProd_morph_rest CRC rco CRC CRC E pfe_cl a b).
exact (Split_pProd_morph_com_1 CRC rco CRC CRC E pfe_cl a b).
exact (Split_pProd_morph_com_2 CRC rco CRC CRC E pfe_cl a b).
exact (Split_pProd_morph_unique CRC rco CRC CRC E pfe_cl a b).
Defined.


(* define terminal object in Split_RC when E contains the id map on the terminal object *)
Definition split_p_term `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)) : (SplitRC C rco CRC E ).
 unfold SplitRC. simpl. unfold split_obj.
exists RCat_term. exists (pt_morph RCat_term).
split. rewrite <- id_is_ptm. auto.
rewrite <- id_is_ptm. rewrite id_unit_right. auto.
Defined.


Definition split_pt_morph `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)) : 
forall (a : (SplitRC C rco CRC E )), Hom a (split_p_term CRC rco CRC CRC E Ehas_id).
 unfold SplitRC. simpl. unfold split_obj.
intro. destruct a as [a [ea pa2]].
unfold split_hom. simpl.
exists ((pt_morph a) ∘ ea). split.
rewrite <- id_is_ptm. auto.
rewrite assoc. destruct pa2 as [pa2 paa2]. rewrite paa2.
auto. Defined.

Definition split_morph_total `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)) : 
forall (a : (SplitRC C rco CRC E )), (SplitRCtype C E rco RC) _ _ (split_pt_morph CRC rco CRC CRC E Ehas_id a) = id a.
Admitted.

Definition split_id_is_ptm `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)) : 
 id (split_p_term CRC rco CRC CRC E Ehas_id) = split_pt_morph CRC rco CRC CRC E Ehas_id  (split_p_term CRC rco CRC CRC E Ehas_id).
Admitted.

Definition split_pt_morph_unique_greatest `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)) : 
forall (a b : (SplitRC C rco CRC E )) (f : Hom a b),
((split_pt_morph CRC rco CRC CRC E Ehas_id b) ∘ f) = 
    (split_pt_morph CRC rco CRC CRC E Ehas_id a) ∘ ((SplitRCtype C E rco RC) _ _  f).
Admitted.


Definition Split_Term  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco) (CRC : @CartRestrictionCat C rco RC)
(E : idem_class C) (Ehas_id : E RCat_term (id RCat_term)):  
@ParTerm (SplitRC C rco CRC E) (Split_rc C rco CRC E ) (SplitRC C rco CRC E ).
exists (split_p_term CRC rco CRC CRC E Ehas_id) (split_pt_morph CRC rco CRC CRC E Ehas_id ) .
exact (split_morph_total CRC rco CRC CRC E Ehas_id ).
exact (split_id_is_ptm CRC rco CRC CRC E Ehas_id ).
exact (split_pt_morph_unique_greatest CRC rco CRC CRC E Ehas_id ).
Defined.


(* instanciate SplitRC as a cartesian restriction category - when E closed under products *)
Instance SplitCRC  `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (E : idem_class C) (pfe_cl : E_closed_prod C rco RC CRC E )
(Ehas_id : E RCat_term (id RCat_term)) : 
  @CartRestrictionCat (SplitC C E) (Split_rc C  rco RC E)  (SplitRC C rco RC E).
exists.
exact (Split_Term CRC rco CRC CRC E Ehas_id ).
exact (Split_Prods CRC rco CRC CRC E pfe_cl ).
 Defined.

Definition all_split `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) : idem_class CRC
:= fun (a : CRC ) (e : Hom a a) => True.

Definition asp `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) : 
E_closed_prod C rco RC CRC (all_split CRC rco CRC CRC  ).
intros. unfold all_split. unfold E_closed_prod. intros. auto. Defined.


Definition h_id `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) : 
(all_split C rco RC CRC ) RCat_term (id RCat_term) .
unfold all_split.  auto. Defined.


(* SplitCompA - without comb. compl. definition with all idempotents split *)
Definition SplitCompA_justCat_allIdem `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (A : CRC) := SplitCRC (CompA_CRCat CRC rco CRC CRC A)
(rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) 
(all_split (CompA_CRCat CRC rco CRC CRC A)
(rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) )
 (asp (CompA_CRCat CRC rco CRC CRC A)
(rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) ) (h_id (CompA_CRCat CRC rco CRC CRC A)
(rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) ) .

Definition E_SplitCompA_justCat `(C : Category) (rco : @RestrictionComb C) (RC : @RestrictionCat C rco)
(CRC : @CartRestrictionCat C rco RC) (A : CRC) (E : idem_class (CompA_CRCat CRC rco CRC CRC A)) (pfe_cl : E_closed_prod _ _ _ _ E )
(Ehas_id : E RCat_term (id RCat_term)) := SplitCRC (CompA_CRCat CRC rco CRC CRC A)
(rcCompA CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) (CompA_CRCat CRC rco CRC CRC A) E 
 pfe_cl Ehas_id.


