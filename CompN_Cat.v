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
Add LoadPath "..\amintimany-categories-bd56bc28cc67\amintimany-categories-bd56bc28cc67\Basic_Cons".

Require Import Main_Category.
Require Import CCC.
Require Import Coq.Setoids.Setoid.
Require Import Logic.
Require Import Restriction.
Require Import Coq.Lists.List.
Require Import Turing.
Require Import Par_Cat.
Require Import PeanoNat Even NAxioms.
Require Import CompA.
Require Import PCA.
Require Import Range.


(*AXIOM proof irrelevance*)
Axiom pf_ir : forall A: Prop , forall p q:A, p=q.


Open Scope nat_scope.

Open Scope list_scope.

Inductive prf : Type := 
| Zero : prf
| Succ : prf 
| Proj : nat -> prf
| Sub : prf -> prf -> nat -> nat -> prf
| Rec : prf -> prf -> prf
| Min : prf -> prf.


Fixpoint blt_nat (n m : nat) : bool.
Proof.
  exact (match m with
          | O => false
          | S m' =>
              match n with
              | O => true
              | S n' => blt_nat n' m'
              end
          end).
Defined.


Fixpoint zel (i : nat) (ln : list nat) : nat :=
 match (blt_nat (length ln) i) with
       | true => 0
       | false => ( match i with | 0 => 0 | S 0 => ( match ln with | nil => 0 | l :: ln' => l end)
                        | S n' => ( match ln with | nil => 0 | l :: ln' => zel n' ln' end) end )
     end.


Fixpoint pcombine (n m : nat) (l : list nat) (x : nat) : list nat :=
  match m with 
           | 0 => match n with | 0 => cons x nil | S n' => cons (zel n l) (cons x nil) end
           | S m' => cons (zel n l) (pcombine (S n) m' l x) 
  end.

(* prf convergence including minimalization *)
Inductive converges_to : prf -> list nat -> nat -> Prop :=
  | conv_zero' : forall (l : list nat), converges_to Zero l 0
  | conv_succ' : converges_to Succ nil (S 0) 
  | conv_succ_nil' : forall (l : list nat), forall x : nat, converges_to Succ (cons x l) (S x) 
  | conv_proj' : forall (l : list nat), forall i : nat, ((blt_nat (length l) i) = false ) ->
          (converges_to (Proj i) l (zel i l))
  | conv_sub' : forall (l : list nat), forall (f g : prf), forall (n m x y : nat), converges_to g l x ->
    converges_to f (pcombine n m l x) y ->
       converges_to (Sub f g n m) l y
  | conv_pr_nil' : forall (B s : prf), forall (x : nat), converges_to B nil x -> converges_to (Rec B s) nil x
  | conv_pr_l' : forall (l : list nat), forall (B s : prf), forall (x : nat), converges_to B l x ->
    converges_to (Rec B s) (cons 0 l) x
  | conv_pr' : forall (l : list nat), forall (B s : prf), forall (x h r: nat), converges_to (Rec B s) (cons h l) r ->
       converges_to s (cons h (cons r l)) x -> converges_to (Rec B s) (cons (S h) l) x 
  | conv_min_z : forall f : prf, forall ln : list nat,  converges_to f (cons 0 ln) 0 ->  
        converges_to (Min f)  ln  0
  | conv_min_Sn_asz : forall f : prf, forall ln : list nat, forall (n : nat), converges_to f (cons (S 0) ln)  0 ->
        converges_to f (cons 0 ln) (S n) ->
        converges_to (Min f)  ln  (S 0)
  | conv_min_Sn_asn : forall f : prf, forall ln : list nat, forall (n : nat), converges_to f (cons (S (S 0)) ln) 0 -> 
        converges_to f (cons (S 0) ln) (S n) ->
        converges_to f (cons 0 ln) (S n) ->
        converges_to (Min f)  ln  (S (S 0))
  | conv_min_Sn_asn' : forall f : prf, forall ln : list nat, forall (x n : nat), converges_to f (cons (S (S x)) ln) 0 -> 
        converges_to f (cons (S x) ln) (S n) ->
        converges_to f (cons (S (S x)) ln) (S n) ->
        converges_to (Min f)  ln  (S x) ->
        converges_to (Min f)  ln  (S (S x)).

Lemma unique_conv : forall f ln y z, converges_to f ln y -> converges_to f ln z -> y=z.
intros.
induction H. try (inversion H0;  auto).
try (inversion H0;  auto). try (inversion H0;  auto).
try (inversion H0;  auto). 
Focus 2. try (inversion H0;  auto). inversion H0.
Focus 4. apply IHconverges_to. inversion H0. auto.
rewrite H5. induction n. rewrite H5 in H3. auto.
Admitted.
(*
inversion H0 contradiction.
rewrite H5.  induction H0.
auto.
apply IHconverges_to2. inversion H0.
inversion H. inversion H8;
try (rewrite <- H10 in H13; inversion H13);
try (rewrite <- H10 in H14; inversion H14);
try (rewrite <- H10 in H15; inversion H15);
try (rewrite <- H10 in H16; inversion H16);
try (rewrite <- H10 in H17; inversion H17).
rewrite <- H15 in H9. auto.
inversion H0.

elim H10.

 inversion H9).

rewrite <- H15 in H9; auto.
rewrite <- H15 in H9.
Focus 8. try (inversion H0;  auto).
try (rewrite <- H1 in H4; inversion H4);
try (rewrite <- H1 in H5; inversion H5);
try (rewrite <- H1 in H6; inversion H6);
try (rewrite <- H1 in H7; inversion H7);
try (rewrite <- H1 in H8; inversion H8).
try (rewrite <- H5 in H2; inversion H2).
try (rewrite <- H5 in H2; inversion H2).

rewrite <- H5
inversion H9.
Focus 15.
rewrite (IHconverges_to4 H0). rewrite


 inversion H2. rewrite H5. rewrite <- H6 in H2.
inversion H2. apply IHconverges_to.

 induction z. apply symmetry. auto. inversion H0. rewrite <- H5 in H9. auto.
rewrite H10. apply IHconverges_to. inversion H0.
rewrite <- H10 in IHconverges_to. rewrite <- H5 in IHconverges_to.
induction n. exact (IHconverges_to H3).
 inversion H0. auto.
inversion H0. auto.




 induction f. inversion H; inversion H0; try auto.
induction ln. inversion H. inversion H0. auto.
inversion H. inversion H0. auto.
induction ln. inversion H. inversion H0. auto.
inversion H. inversion H0. auto.
induction ln. inversion H. inversion H0.
Focus 4. induction ln. inversion H.
rewrite <- H4 in IHf. apply IHf.
 inversion H2. econstructor. simpl in H8.
induction i. simpl. econstructor. simpl. auto.
simpl. simpl in IHi. rewrite H8. intuition.
assert (i=0). induction i. auto. inversion H8. rewrite H9. 
econstructor. simpl. rewrite H9 in H5. simpl in H5.
generalize (conv_proj' nil (S i)). simpl. intro. 
apply conv_proj'. econstructor. simpl. inversion H8. destruct H. 
destruct H.  destruct H0; try auto. apply IHf. simpl. econstructor.

inversion H6. inversion H.
induction ln. inversion H. inversion H0.
compute in H8
inversion H8. inversion H16. auto.
inversion H16. rewrite <- H23 in H20.
generalize H25. inversion H20. inversion H0. auto.

Inductive converges_to_prim : prf -> list nat -> nat -> Prop :=
  | conv_zero'' : forall (l : list nat), converges_to_prim Zero l 0
  | conv_succ'' : converges_to_prim Succ nil (S 0) 
  | conv_succ_nil'' : forall (l : list nat), forall x : nat, converges_to_prim Succ (cons x l) (S x) 
  | conv_proj'' : forall (l : list nat), forall i : nat, ((blt_nat (length l) i) = false ) ->
          (converges_to_prim (Proj i) l (zel i l))
  | conv_sub'' : forall (l : list nat), forall (f g : prf), forall (n m x y : nat), converges_to_prim g l x ->
    converges_to_prim f (pcombine n m l x) y ->
       converges_to_prim (Sub f g n m) l y
  | conv_pr_nil'' : forall (B s : prf), forall (x : nat), converges_to_prim B nil x -> converges_to_prim (Rec B s) nil x
  | conv_pr_l'' : forall (l : list nat), forall (B s : prf), forall (x : nat), converges_to_prim B l x ->
    converges_to_prim (Rec B s) (cons 0 l) x
  | conv_pr'' : forall (l : list nat), forall (B s : prf), forall (x h r: nat), converges_to_prim (Rec B s) (cons h l) r ->
       converges_to_prim s (cons h (cons r l)) x -> converges_to_prim (Rec B s) (cons (S h) l) x 
.*)

(*
Lemma prim_total : forall f ln, exists y, converges_to_prim f ln y.
intros. induction f. exists 0. econstructor.
induction ln. exists (S 0). econstructor. exists (S a). econstructor.
induction ln. induction n. generalize (conv_proj'' nil 0). intro.
exists (zel 0 nil). apply H. compute. auto. Focus 3.
destruct IHf1. destruct IHf2.
generalize (conv_sub'' ln f1 f2 n n0 x0 x H0). intros.
exists x. apply H1. induction ln. simpl. unfold pcombine. simpl.  H) .
*)


(* define the CRC of all maps of type N^n -> N^m *)
Definition CompsNR := all_prod_maps_Rcat Par_Cat rc_Par Par_isRC Par_isCRC nat.  

Definition CompNRC := (CompA_CRCat Par_Cat rc_Par Par_isRC Par_isCRC nat) .

Definition rc_CompN := rcCompA Par_Cat rc_Par Par_isRC Par_isCRC nat : RestrictionComb CompsNR.

Definition CompNCRC := CompA_CRCat Par_Cat rc_Par Par_isRC Par_isCRC nat .



(* enumerate all prf's *)
Definition enum_prf (f : prf) : nat. Admitted.

(* obtain the prf corresponding to given n *)
Definition nat_to_prf (n : nat) : prf. Admitted.

(* prove that enum_prf and nat_to_prf are inverse operations of each other *)
Lemma nat_prf_nat : forall (n : nat) ,  (enum_prf (nat_to_prf n)) = n.
Admitted.

Lemma prf_nat_prf : forall (f : prf) ,  (nat_to_prf (enum_prf f)) = f.
Admitted.


(* object 1 x N *)
Definition obj_nat : CompsNR.
unfold CompsNR. unfold all_prod_maps_Rcat.
exists (prod nat  par_p_term). exists 1. simpl.
unfold par_p_prod. auto.
Defined.

(* axiom of choice of selecting a (unique) nat number y such that a prf f converges to it on a given list *)
Definition AC_select_y (ln : list nat) (f : prf) (pf_ex : exists (y: nat), (converges_to f ln y))  : nat.
Admitted.

Axiom AC_rewrite : forall (ln : list nat) (f : prf) (pf_ex : exists (y: nat), (converges_to f ln y)) ,
converges_to f ln (AC_select_y ln f pf_ex).


(* axiom of unique choice for selecting the n for an object of type N^n in the CompsNR full subcategory of Par_Cat *)
Definition AC_select_Product (x : Par_isCRC) (pf_prod : exists (n : nat), x = @nthProdC Par_Cat rc_Par Par_isRC Par_isCRC nat n )  : nat.
Admitted.

(* axion of unique choice *)
Axiom AC_Prod_rewrite : forall (x : Par_isCRC) (pf_prod : exists (n : nat), x = @nthProdC Par_Cat rc_Par Par_isRC Par_isCRC nat n ) ,
x =  @nthProdC Par_Cat rc_Par Par_isRC Par_isCRC nat (AC_select_Product x pf_prod)    /\
    (forall (y:nat), (x = @nthProdC Par_Cat rc_Par Par_isRC Par_isCRC nat y) -> (y = (AC_select_Product x pf_prod))).


Definition build_compsNR_obj (n : nat) : CompsNR.
destruct CompsNR. simpl. eexists.
Unshelve. exists n. apply reflexivity.
Defined.

(* object b is the same object as N^n for n selected via AC_select_Product *)
Lemma re_build_obj : forall b, (build_compsNR_obj (AC_select_Product (proj1_sig b) (proj2_sig b) ) = b).
intro. destruct b. unfold build_compsNR_obj. simpl.
apply exist_eq. rewrite (proj1 (AC_Prod_rewrite x e )). auto.
Defined.

(* make an object in the CompsNR category into a list of natural numbers *)
Definition N_toProd (a : CompsNR) (x : proj1_sig a) :  list nat.
generalize x. generalize ( re_build_obj a). simpl. intro. rewrite <- H.
 destruct a. simpl. induction (AC_select_Product x0 e). intro. exact nil.
simpl. intro. 
assert ((npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n)) 
      = (nthProdC rc_Par nat n)). simpl. auto. rewrite H0 in x1.
destruct x1. exact (fst :: (IHn snd)).
Defined.

(* make a prf into a map in the CompsNR category *)
Definition prf_par_map (f : prf) (x : CompsNR) :
  @hom (proj1_sig x) nat.
unfold hom. eexists; try auto. intro. Unshelve. 
Focus 2. intro. exact (exists (y: nat), (converges_to f (N_toProd x H) y)).
intros. exact ((AC_select_y (N_toProd x x0) f H) ). 
Defined. 

Definition pr1 (a : CompsNR) (n : nat) (H : proj1_sig a = nthProdC rc_Par nat (S n)) :
hom (proj1_sig a) nat .
destruct a. simpl in H. simpl. rewrite H. unfold hom. eexists.
Unshelve. Focus 2. intro. exact True. intro. simpl. intro. exact (fst x0).
Defined.

Definition pr1f (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m)):
hom (proj1_sig (build_compsNR_obj n)) nat .
simpl. simpl in f. destruct f. induction m.
eexists. intros. exact 0.
eexists. destruct x. intros. Unshelve. Focus 2.
destruct x. exact x. Focus 2. destruct x. exact x.
simpl in H. exact (fst (n0 x0 H)).
Defined.

Definition pr2Cf (a b : CompsNR) (f : hom (proj1_sig a) (proj1_sig b)) (n : nat) (H : proj1_sig b = nthProdC rc_Par nat (S n)) :
@Hom CompsNR a (build_compsNR_obj n).
destruct a. simpl. destruct b. simpl in H. eexists; try auto.
rewrite H in f. destruct f. simpl in x1.
 unfold hom. exists x1. 
intros. simpl in p.
exact (snd (p x2 H0)).  
Defined.

Definition into_term (n : nat) (f : Hom (build_compsNR_obj n) (build_compsNR_obj 0) ) : 
@hom (proj1_sig (build_compsNR_obj n)) nat.
unfold hom. destruct f. destruct x. exists x. intros.
induction n. exact 0. simpl in x. simpl in x0. simpl in p.
destruct x0. exact fst.
Defined.

(*
Definition conv_to_cat_one (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m))
(R : forall ( n' m' : nat) (f : @Hom CompsNR (build_compsNR_obj n') (build_compsNR_obj m')), Prop)
: Prop. 
 destruct m. exact True. (* destruct n.
 simpl in f. destruct f. destruct x. exact (((x tt) = False) /\ ((x tt) = True)). 
exact  (exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj (S n)) =  into_term (S n) f ). 
destruct m. 
destruct f as [f].
assert (H : proj1_sig (build_compsNR_obj 1) = nthProdC rc_Par nat 1). simpl. auto.
exact ( (exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj n) =  ((pr1 (build_compsNR_obj 1) 0 H) ∘ f) )  ). *)
destruct m. exact True.
destruct f as [f]. assert (H : proj1_sig (build_compsNR_obj (S (S m))) = nthProdC rc_Par nat (S (S m))).
simpl. auto. 
exact ( (exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj n) =  ((pr1 (build_compsNR_obj (S (S m))) (S m) H) ∘ f) )   /\
    (R n (S m) (pr2Cf (build_compsNR_obj n) (build_compsNR_obj (S (S m))) f (S m) H) )).  
Defined.
*)

Definition conv_to_cat_zero
  (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m))
(test_prop : ∀ n m : nat, @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m) -> Prop) : Prop.
 destruct n.  destruct f as [f]. simpl in f.
 exact (exists prf_f : prf, projT1 (prf_par_map prf_f RCat_term) tt ↔ projT1 f tt).
destruct m. exact True.
assert (H : proj1_sig (build_compsNR_obj (S n)) = nthProdC rc_Par nat (S n)). simpl. auto.
destruct f as [f]. 
assert (H1 : proj1_sig (build_compsNR_obj (S m)) = nthProdC rc_Par nat (S m)). simpl. auto.
exact  ((exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj (S n)) = 
   ((pr1 (build_compsNR_obj (S n)) n H) ∘ (@rc _ rc_Par _ _ f)) ) /\
(test_prop (S n) m (pr2Cf (build_compsNR_obj (S n)) (build_compsNR_obj (S m)) f m H1) )) .
Defined. 

Fixpoint conv_to_cat_zero_fix (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m))
: Prop := 
match m with 
  | 0 => True
  | S m' => (conv_to_cat_zero n m f conv_to_cat_zero_fix)
end.


Definition  conv_to_cat_one
  (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m))
(test_prop : ∀ n m : nat, @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m) -> Prop) : Prop.
destruct m. 
exact (conv_to_cat_zero_fix n n (@rc _ rc_CompN _ _ f)).
destruct f as [f]. assert (H : proj1_sig (build_compsNR_obj (S m)) = nthProdC rc_Par nat (S m)).
simpl. auto. 
exact ((exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj n) =  ((pr1 (build_compsNR_obj (S m)) m H) ∘ f) )  /\
(test_prop n m (pr2Cf (build_compsNR_obj n) (build_compsNR_obj (S m)) f m H) )) . Defined. 

Fixpoint conv_to_cat_prop (n m : nat) (f : @Hom CompsNR (build_compsNR_obj n) (build_compsNR_obj m))
: Prop := 
match m with 
 | 0 => (conv_to_cat_zero_fix n n (@rc _ rc_CompN _ _ f))
 | S 0 => (exists (prf_f : prf) , prf_par_map prf_f (build_compsNR_obj n) =  (pr1f n m f)) 
 | S (S m') => (conv_to_cat_one n m f conv_to_cat_prop)
end.


Fixpoint x_out (x : nat) : prf :=
match x with 
  | 0 => Zero
  | S x' => Sub Succ (x_out x') 0 0 
end.


Definition test_x_out : forall x ln, converges_to (x_out x) ln x.
intros. compute. induction x. econstructor. 
econstructor. 
exact IHx. econstructor.
Defined.

Lemma points_comp : forall y , exists f, converges_to f nil y.
intros. exists (x_out y).
apply test_x_out.
Defined. 

Lemma undefined_point :
exists f, forall y, converges_to f nil y -> False.
eexists. intros. Unshelve. Focus 2. 
exact (Min (x_out (S 0))).
inversion H. inversion H1.
simpl in H11. inversion H11.
inversion H1. simpl in H12.
 inversion H12.
inversion H1. simpl in H13. inversion H13.
inversion H1. simpl in H14. inversion H14.
Defined.

(*
Lemma term_maps_prf : 
forall (f : hom (proj1_sig (@p_term  CompNCRC rc_CompN CompNCRC (@RCat_term CompNCRC rc_CompN CompNCRC CompNCRC))) nat), 
(((projT1 f) tt) (*\/ (((projT1 f) tt) -> False)*)) ->
exists prf_f, prf_par_map prf_f (@RCat_term CompNCRC rc_CompN CompNCRC CompNCRC) =  f.
intros. destruct f. unfold prf_par_map. eexists. rewrite <- par_eqv_def. unfold HomParEqv. 
split; intros; try split; try intros. simpl in z. unfold par_p_term in z. 
destruct z. simpl in H. auto. simpl in x. simpl in n. destruct z. simpl in H.
 exists (n tt H). simpl.  replace ( N_toProd (CompAterm Par_Cat rc_Par Par_isRC Par_isCRC nat) tt) with (@nil nat).
 Unshelve. Focus 4. simpl in H. exact (x_out (n tt H)). 
apply test_x_out. Focus 2. destruct z. replace pf1 with H. Focus 2. apply pf_ir.

apply (unique_conv (x_out (n tt H)) (N_toProd RCat_term tt)).
assert (n z pf1 = n tt H). assert (z =tt). destruct z; auto. rewrite pf_ir. simpl in x.
 unfold par_p_term in x. exists (x_out *)


Definition prf_par_map (f : prf) (x : CompsNR) :
  @hom (proj1_sig x) nat.

Definition Comp_mapsN (a b : CompsNR) (f : @Hom CompsNR a b) : Prop.
replace a with (build_compsNR_obj (AC_select_Product (proj1_sig a) (proj2_sig a))) in f.
replace b with (build_compsNR_obj (AC_select_Product (proj1_sig b) (proj2_sig b))) in f.
exact (conv_to_cat_prop (AC_select_Product (proj1_sig a) (proj2_sig a)) (AC_select_Product (proj1_sig b) (proj2_sig b)) f).
apply re_build_obj. apply re_build_obj.
Defined.


Definition idXid (a : CompsNR) : @Hom CompsNR (build_compsNR_obj (AC_select_Product (proj1_sig a) (proj2_sig a)))
  (build_compsNR_obj (AC_select_Product (proj1_sig a) (proj2_sig a))).
eexists.
destruct a; simpl. induction (AC_select_Product x e). simpl.
exact id. simpl. unfold hom.
eexists. Unshelve. Focus 3. intro. destruct IHn. destruct H.
exact  (x0 snd). intros. destruct IHn. destruct x0. exists.
exact fst. exact snd. exact I.
Defined.


Lemma id_CompsN_Coor (a : CompsNR) : id (build_compsNR_obj (AC_select_Product (proj1_sig a) (proj2_sig a))) = idXid a.
unfold id. simpl.  
unfold idXid. apply exist_eq. destruct a. simpl. 
induction (AC_select_Product x e). simpl. auto.
unfold nat_rect in IHn. simpl in IHn. induction n.
simpl. unfold Id. apply par_eqv_def. simpl. split. intros; try tauto.
intros. destruct z. auto. simpl.
unfold par_p_prod. unfold Id. simpl.
unfold Id in IHn. simpl in IHn.
apply par_eqv_def. simpl.
apply par_eqv_def in IHn. simpl in IHn.
destruct IHn. split. intro. split. intro. destruct z as [z1 z2].
 destruct (H z2). destruct z2. simpl. apply (H2 I). 
intros. auto. intros. destruct z as [z1 z2].
destruct z2 as [z2 z22]. simpl.
destruct (z1, (z2, z22)). auto.
Defined.

Lemma obj_list : forall n fs sn,  (N_toProd (build_compsNR_obj (S n)) (fs, sn)) = (fs :: (N_toProd (build_compsNR_obj n) (sn)) ).
simpl. intros.
unfold N_toProd. destruct n. Admitted.


Definition id_fix_one : forall  (n : nat) 
 (R : ∀ (n' : nat)  ,
         conv_to_cat_prop n' n' id), conv_to_cat_prop n n id.
assert (forall l : list nat, blt_nat (length l) 0 = false). 
induction l. simpl. auto. simpl. auto.  unfold id. (*
simpl. induction n. simpl. tauto. unfold Id. unfold hom.
destruct (nthProdC rc_Par nat (S n)).
destruct Par_Cat. simpl. unfold nthProdC. simpl. induction n. Focus 2.
assert ( (exist (λ _ : hom (nthProdC rc_Par nat (S (S n))) (nthProdC rc_Par nat (S (S n))), True)
     (Id (nthProdC rc_Par nat (S (S n)))) I)
 = (exist (λ _ : hom (nthProdC rc_Par nat (S (S n))) (nthProdC rc_Par nat (S (S n))), True)
     (Id (nthProdC rc_Par nat (S (S n)))) I)).

generalize AC_Prod_rewrite. intro.

generalize (id_CompsN_Coor (build_compsNR_obj n)).
induction n. simpl. tauto. simpl. split. 
exists (Proj 1). unfold prf_par_map. 
apply par_eqv_def. simpl. split. intros. split; intro; try tauto.
destruct z. exists fst. 
generalize ( conv_proj' (N_toProd (build_compsNR_obj (S n)) (fst, snd)) 1). simpl.
intro.  rewrite obj_list. simpl.
generalize (conv_proj' (fst :: N_toProd (build_compsNR_obj n) snd) 1). simpl.
intro. assert (((if blt_nat (length (N_toProd (build_compsNR_obj n) snd)) 0  then 0 else fst)) = fst).
Focus 2.
assert (blt_nat (length (N_toProd (build_compsNR_obj n) snd)) 0 = false). Focus 2. 
rewrite H4 in H3. exact (H3 H5). apply H. rewrite H. auto. intros. destruct z. simpl.
destruct pf1. destruct H1. 
generalize (conv_proj' (fst :: N_toProd (build_compsNR_obj n) snd) 1). 
simpl. rewrite H. intros. rewrite <- (obj_list n fst snd) in H2.
generalize (unique_conv (Proj 1) (N_toProd (build_compsNR_obj (S n)) (fst, snd)) (AC_select_y (N_toProd (build_compsNR_obj (S n)) (fst, snd)) (Proj 1) pf)).
intro. generalize (AC_rewrite (N_toProd (build_compsNR_obj (S n)) (fst, snd)) (Proj 1) pf).
intro. apply H3. auto. apply H2. auto.  

unfold par_p_prod. unfold nthProdC. simpl. destruct Par_isCRC.
 destruct prod.
destruct ((exist
     (λ
      _ : hom (nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n))
            (nthProdC rc_Par nat n), True)
     (existT
        (λ P : nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n) → Prop,
         ∀ x : nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n),
         P x → nthProdC rc_Par nat n)
        (λ _ : nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n), True)
        (λ (x2 : nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n))
         (_ : True), snd x2)) I)).
induction n.


Focus 2. simpl. unfold par_p_prod. simpl. exists.
exists (Proj 1).
 destruct (par_p_prod nat
                 (par_p_prod nat
                    (npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n)))).
 destruct (hom (nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n))
            (nthProdC rc_Par nat n), True).  (nat * npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n)).
(par_p_prod nat (npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n))).
generalize (R n); intros.
assert (proj1_sig (build_compsNR_obj (S n)) =
 nthProdC rc_Par nat (S n)). Focus 2.
replace (conv_to_cat_prop (S n) n _ ) with (conv_to_cat_prop (S n) n (pr2Cf _ _ (id _) n H2 )).
simpl. unfold conv_to_cat_prop. simpl. Focus 2. simpl. 
assert (forall q p, q = p -> (conv_to_cat_prop (S n) n p = conv_to_cat_prop (S n) n q)).
intros q p  HH; rewrite HH; auto. apply H3. apply exist_eq. apply par_eqv_def.
simpl. unfold par_p_prod. 
unfold hom. unfold Id.  unfold eq_rect. unfold eq_refl.
replace  (npobj rc_Par (nthProdC rc_Par nat n) (nthProdC rc_Par nat n)) with (nthProdC rc_Par nat n).

 induction n. simpl. split. intros. split. 
replace (_) with (pr2Cf _ _ (idXid (build_compsNR_obj (S n)))).
inversion H0. induction n. simpl in H3. unfold Id in H3. 
unfold conv_to_cat_prop. simpl. Focus 2. simpl.
split.  exists (Proj 1). unfold prf_par_map.
apply par_eqv_def. unfold HomParEqv. split. 
intro. Focus 3. unfold conv_to_cat_prop. simpl.
unfold conv_to_cat_one. simpl. split.

 assert (Id (nthProdC rc_Par nat
          (AC_select_Product _ _ )) = Id (nthProdC rc_Par nat n)).
simpl. destruct (idXid (build_compsNR_obj (S n))).
inversion H0. destruct x as [f1 f2]. unfold Id in H3.
apply par_eqv_def in H3. unfold HomParEqv in H3.
 unfold conv_to_cat_prop. unfold conv_to_cat_one. simpl.
(S n) n).
apply exist_eq.
simpl in H0. unfold conv_to_cat_prop. simpl.

 unfold N_toProd
replace (N_toProd (build_compsNR_obj (S n)) (fst, snd)) with 
    (fst :: (N_toProd (build_compsNR_obj n) (snd)) ). simpl.

assert  ((blt_nat (length (N_toProd (build_compsNR_obj n) snd)) 0 = false)).
unfold blt_nat. simpl. 
generalize (conv_proj' (fst :: (N_toProd (build_compsNR_obj n) (snd)) ) 1). unfold zel.
simpl. intro. apply H0. 
destruct ( (fst :: N_toProd (build_compsNR_obj n) snd)) . simpl. Focus 2. simpl.

destruct (length (fst :: N_toProd (build_compsNR_obj n) snd)) .
unfold blt_nat.
simpl. intro.

Focus 4. exact (R (S n) n _). (* unfold par_p_prod.  conv_to_cat_prop. simpl. 
exact (R n). unfold N_toProd. simpl. auto. apply H0.  
 constructor conv_proj'.
unfold N_toProd. simpl.
 replace (N_toProd (build_compsNR_obj (S n)) (fst, snd)) with (fst, snd). econstructor.
 simpl. *) *) Admitted.

Definition idXidn (n : nat) : @Hom CompsNR (build_compsNR_obj n)
  (build_compsNR_obj n). 
replace (build_compsNR_obj n) with ((build_compsNR_obj
     (AC_select_Product 
        (proj1_sig (build_compsNR_obj n)) 
        (proj2_sig (build_compsNR_obj n))))) . exact (idXid (build_compsNR_obj n)).
rewrite <- re_build_obj. auto. 
Defined.

Definition id_fix  (n : nat) : conv_to_cat_prop n n (idXidn n) .
unfold idXidn. induction n.
unfold conv_to_cat_prop. simpl. Focus 2. 
unfold idXid. unfold conv_to_cat_prop. simpl. 
unfold par_p_prod. Admitted.

(* id is computable - exists a list of prfs that computes it *)
Definition id_comp_a  (a : CompsNR) : Comp_mapsN a a id.
Admitted.

(* composition is computable - exists a list of prfs that computes it *)
Definition comp_comp_abc (a b c : CompsNR) (f : @Hom CompsNR a b) (g : @Hom CompsNR b c) :
Comp_mapsN a b f -> Comp_mapsN b c g -> Comp_mapsN a c (g ∘ f).
Admitted.


(* CompN is a wide subcategory of computable maps in CompsNR *)
Definition CompN : Category.
  apply (Wide_SubCategory CompsNR (Comp_mapsN ));
intros. exact (id_comp_a a). exact (comp_comp_abc a b c f g H H0 ).
Defined.



Definition rc_in_CompN : forall (a b : CompN) (f : @Hom CompN a b), 
    Comp_mapsN _ _  (@rc CompsNR rc_CompN  (proj1_sig a) (proj1_sig b) (proj1_sig f)).
Admitted.

Definition rcCompN : RestrictionComb CompN.
eexists. Unshelve. Focus 5. eexists. Unshelve.
Focus 2. exact (@rc CompsNR rc_CompN  (proj1_sig a) (proj1_sig b) (proj1_sig X)).
exact (rc_in_CompN a b X).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. apply (@rc1 CompsNR rc_CompN).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. apply (@rc2 CompsNR rc_CompN).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. apply (@rc3 CompsNR rc_CompN).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. apply (@rc4 CompsNR rc_CompN).
Defined.

Instance CompN_RC : RestrictionCat CompN rcCompN.
exists. Defined.


Definition ComNprod (a b : CompN_RC) : CompN_RC .
try destruct a as [a]; try destruct b as [b].
exists (RCat_HP a b). auto.
Defined.

Lemma pi1_comp (a b : CompN_RC) : Comp_mapsN (CompAprod Par_Cat rc_Par Par_isRC Par_isCRC nat (proj1_sig a) (proj1_sig b)) 
  (proj1_sig a) (@Pi_1p CompsNR rc_CompN CompNRC (proj1_sig a) (proj1_sig b) (RCat_HP (proj1_sig a) (proj1_sig b))).
Admitted.

Lemma pi2_comp (a b : CompN_RC) : Comp_mapsN (CompAprod Par_Cat rc_Par Par_isRC Par_isCRC nat (proj1_sig a) (proj1_sig b)) 
  (proj1_sig b) (@Pi_2p CompsNR rc_CompN CompNRC (proj1_sig a) (proj1_sig b) (RCat_HP (proj1_sig a) (proj1_sig b))).
Admitted.

Definition CompNPi_1p (a b : CompN_RC) : Hom (ComNprod a b) a .
generalize (pi1_comp a b). intros.
destruct a as [a]; destruct b as [b]; simpl.
exists (@Pi_1p CompsNR rc_CompN CompNRC a b (RCat_HP a b)).
simpl in H. auto.
Defined.

Definition CompNPi_2p (a b : CompN_RC) : Hom (ComNprod a b) b .
generalize (pi2_comp a b). intros.
destruct a as [a]; destruct b as [b]; simpl.
exists (@Pi_2p CompsNR rc_CompN CompNRC a b (RCat_HP a b)).
simpl in H. auto.
Defined.

Definition  CompNPi_1Tot (a b : CompN_RC) : @rc CompN_RC rcCompN _ _ (CompNPi_1p a b) = id (ComNprod a b).
destruct a as [a]; destruct b as [b]; simpl. apply exist_eq.
generalize (@Pi_1Tot CompsNR rc_CompN CompNRC a b (RCat_HP a b)). simpl.
intro. auto.
Defined.

Definition  CompNPi_2Tot (a b : CompN_RC) : @rc CompN_RC rcCompN _ _ (CompNPi_2p a b) = id (ComNprod a b).
destruct a as [a]; destruct b as [b]; simpl. apply exist_eq.
generalize (@Pi_2Tot CompsNR rc_CompN CompNRC a b (RCat_HP a b)). simpl.
intro. auto.
Defined.

Lemma pProd_morph_ex_comp_lem : forall (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) 
    , Comp_mapsN (proj1_sig c)  (CompAprod Par_Cat rc_Par Par_isRC Par_isCRC nat (proj1_sig a) (proj1_sig b)) 
  (@pProd_morph_ex CompsNR rc_CompN CompNRC (proj1_sig a) (proj1_sig b) (RCat_HP (proj1_sig a) (proj1_sig b)) 
        (proj1_sig c) (proj1_sig r1) (proj1_sig r2)).
Admitted.

Definition pProd_morph_ex_comp (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) :
 Hom c (ComNprod a b) .
generalize ( pProd_morph_ex_comp_lem a b c r1 r2).
destruct a as [a]; destruct b as [b]; destruct c as [c]; simpl.
simpl in r1. simpl in r2. destruct r1. destruct r2.
exists (@pProd_morph_ex CompsNR rc_CompN CompNRC a b (RCat_HP a b) c x x0).
auto. Defined.

Definition pProd_morph_rest_comp (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) :
(@rc CompN_RC rcCompN _ _ r1) ∘ (@rc CompN_RC rcCompN _ _ r2) = @rc CompN_RC rcCompN c (ComNprod a b) (pProd_morph_ex_comp a b  c r1 r2) .
destruct a as [a]; destruct b as [b]; destruct c as [c]; simpl.
simpl in r1. simpl in r2. destruct r1 as [r1]. destruct r2 as [r2]. simpl.
apply exist_eq. 
generalize (@pProd_morph_rest CompsNR rc_CompN CompNRC a b (RCat_HP a b) c r1 r2). simpl.
intro. auto.
Defined.

Definition pProd_morph_com_1_comp (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) :
lt_eq _ _ ((CompNPi_1p a b) ∘ (pProd_morph_ex_comp a b  c r1 r2))  r1.
destruct a as [a]; destruct b as [b]; destruct c as [c]; simpl.
simpl in r1. simpl in r2. destruct r1 as [r1]. destruct r2 as [r2]. simpl.
apply exist_eq. 
generalize (@pProd_morph_com_1 CompsNR rc_CompN CompNRC a b (RCat_HP a b) c r1 r2). simpl.
intro. auto.
Defined.

Definition pProd_morph_com_2_comp (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) :
lt_eq _ _ ((CompNPi_2p a b) ∘ (pProd_morph_ex_comp a b  c r1 r2))  r2.
destruct a as [a]; destruct b as [b]; destruct c as [c]; simpl.
simpl in r1. simpl in r2. destruct r1 as [r1]. destruct r2 as [r2]. simpl.
apply exist_eq. 
generalize (@pProd_morph_com_2 CompsNR rc_CompN CompNRC a b (RCat_HP a b) c r1 r2). simpl.
intro. auto.
Defined.

Definition  pProd_morph_unique_comp (a b c : CompN_RC) (r1 : Hom c a) (r2 : Hom c b) (pm : Hom c (ComNprod a b)) 
  (H1 : lt_eq _ _ ((CompNPi_1p a b) ∘ pm)  r1)     (H2 : lt_eq _ _ ((CompNPi_2p a b) ∘ pm)  r2)  
        (H3 : ((@rc CompN_RC rcCompN _ _ r1) ∘ (@rc CompN_RC rcCompN  c b r2) ) = (@rc CompN_RC rcCompN _ (ComNprod a b) pm) ): 
  pm = pProd_morph_ex_comp a b  c r1 r2 .
destruct a as [a]; destruct b as [b]; destruct c as [c]; simpl.
simpl in r1. simpl in r2. destruct r1 as [r1]. destruct r2 as [r2].
destruct pm as [pm]. simpl.
apply exist_eq. simpl in pm. simpl in H1. inversion H1.
simpl in H2. inversion H2. simpl in H3. inversion H3.
generalize (@pProd_morph_unique CompsNR rc_CompN CompNRC a b (RCat_HP a b) c r1 r2 pm). simpl.
intro. apply H. auto. auto. auto.  
Defined.


Definition CompN_Prods (a b : CompN_RC) : ParProd a b  .
exists (ComNprod a b) (CompNPi_1p a b) (CompNPi_2p a b) (pProd_morph_ex_comp a b).
exact (CompNPi_1Tot a b). exact (CompNPi_2Tot a b).
exact (pProd_morph_rest_comp a b). exact (pProd_morph_com_1_comp a b).
exact (pProd_morph_com_2_comp a b). exact (pProd_morph_unique_comp a b).
Defined.

Definition  term_comp : CompN_RC.
exists (@RCat_term CompNCRC rc_CompN CompNCRC CompNCRC). auto.
Defined.

Lemma pt_moph_comp_lem : forall (a : CompN_RC), Comp_mapsN  (proj1_sig a) (proj1_sig term_comp)  (@pt_morph CompNCRC rc_CompN CompNCRC  RCat_term(proj1_sig a)).
Admitted.

Definition pt_morph_comp (a : CompN_RC) : Hom a term_comp.
exists (@pt_morph CompNCRC rc_CompN CompNCRC  RCat_term (proj1_sig a)).
exact (pt_moph_comp_lem a).
Defined.

Definition  morph_total_comp (a : CompN_RC) : @rc CompN_RC rcCompN _ _ (pt_morph_comp a) = id a.
destruct a as [a]. simpl. apply exist_eq. 
generalize (@morph_total CompNCRC rc_CompN CompNCRC  RCat_term a). simpl. auto.
Defined.

Definition  id_is_ptm_comp  : id term_comp = pt_morph_comp term_comp.
simpl. unfold pt_morph_comp. apply exist_eq.
generalize (@id_is_ptm CompNCRC rc_CompN CompNCRC  RCat_term ). simpl. auto.
Defined.

Definition  pt_morph_unique_greatest_comp (a b : CompN_RC) (f : Hom a b)
  : ((pt_morph_comp b) ∘f) = (pt_morph_comp a) ∘ @rc CompN_RC rcCompN _ _ f.
destruct a as [a]. destruct b as [b]. simpl. apply exist_eq. 
destruct f as [f]. simpl.
generalize (@pt_morph_unique_greatest CompNCRC rc_CompN CompNCRC  RCat_term a b f). simpl. auto.
Defined.

Definition Term_compN : @ParTerm CompN_RC rcCompN CompN_RC.
exists term_comp pt_morph_comp.
exact (morph_total_comp). exact id_is_ptm_comp.
exact pt_morph_unique_greatest_comp.
Defined.

Instance CRC_CompN : CartRestrictionCat rcCompN  .
exists. exact Term_compN. exact CompN_Prods. Defined.

Definition N_obj : CompN_RC.
eexists. eexists. Unshelve.
Focus 3. exact (nthProdC rc_Par nat 1).
exists 1. auto. auto.
Defined.

(* bullet defined as a map in the underlying category of all N^n -> N^m maps *)
Definition bullet_CompN_all : @Hom CompNCRC (@RCat_HP CompNCRC rc_CompN CompNCRC CompNCRC (proj1_sig N_obj) (proj1_sig N_obj)) (proj1_sig N_obj).
unfold Hom.
eexists; try auto. 
eexists. Unshelve. Focus 2.
simpl. unfold par_p_prod.
 intro. destruct H as [[fs1 fs2] [sn1 sn2]].
exact (exists (y : nat) , converges_to  (nat_to_prf fs1) (sn1 :: nil) y).
intro. destruct x as [[fs1 fs2] [sn1 sn2]]. intro. simpl. exists.
exact (AC_select_y (sn1 :: nil) (nat_to_prf fs1) H).
exists. 
Defined.


Definition n_obj_rw : (proj1_sig N_obj) = (build_compsNR_obj 1).
simpl. unfold build_compsNR_obj. simpl. apply exist_eq. auto. Defined.

(*
Definition n_obj_rw2 : p_prod (proj1_sig N_obj) (proj1_sig N_obj) (@RCat_HP CompNCRC rc_CompN CompNCRC CompNCRC (proj1_sig N_obj) (proj1_sig N_obj)) = (build_compsNR_obj 2).
simpl. unfold build_compsNR_obj. simpl. apply exist_eq. auto.
*)


Definition bullet_CompN_all_n :  @Hom CompsNR (build_compsNR_obj 2) (build_compsNR_obj 1).
unfold Hom.
eexists; try auto. 
eexists. Unshelve. Focus 2.
simpl. unfold par_p_prod.
 intro. destruct H as [fs1 [sn1 sn2]].
exact (exists (y : nat) , converges_to  (nat_to_prf fs1) (sn1 :: nil) y).
intro. simpl in x.
 destruct x as [fs1  [sn1 sn2]]. intro. simpl. exists.
exact (AC_select_y (sn1 :: nil) (nat_to_prf fs1) H).
exists. 
Defined.

(*
Lemma comps_bullet_n : conv_to_cat_prop 2 1 bullet_CompN_all_n.
unfold conv_to_cat_prop. simpl. split.
exists (Proj 1). unfold prf_par_map. apply par_eqv_def.
simpl. split. intros. destruct z as [z1 [z2 zt]].  
 split; intros. split. destruct H. simpl in H. 
Focus 3. 

 destruct z.
*)

Definition comps_bullet : Comp_mapsN _ _ bullet_CompN_all.
(*
unfold Comp_mapsN.
induction (AC_select_Product
     (proj1_sig (RCat_HP (proj1_sig N_obj) (proj1_sig N_obj)))
     (proj2_sig (RCat_HP (proj1_sig N_obj) (proj1_sig N_obj)))).
 rewrite <- n_obj_rw . simpl. unfold conv_to_cat_prop. 
simpl. rewrite AnAm_Anm_pf. *)
Admitted.

(* bullet defined in Comp(N) *)
Definition bullet_CompN : @Hom CRC_CompN (@RCat_HP CRC_CompN rcCompN CRC_CompN CRC_CompN N_obj N_obj) N_obj.
exists bullet_CompN_all. 
exact comps_bullet.
Defined.

(*
Lemma compsRange : forall a b f, Comp_mapsN b b (@rrc CompNCRC rc_CompN CompNCRC CompNRangeComb a b f).
Admitted.
*)

Definition rrc_in_CompN : @RangeComb CRC_CompN rcCompN CRC_CompN.
eexists. Unshelve. Focus 5.
eexists; try auto. Unshelve. Focus 2. destruct a as [a]. destruct b as [b]. destruct X as [X].  
destruct a. destruct b. destruct X. simpl in x1.
simpl. exists ( @rrc Par_isCRC rc_Par Par_isCRC rrc_Par _ _ x1); try auto. simpl.
Admitted. (*
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g;
apply exist_eq; simpl; try (  apply (@rrc1  Par_Cat rc_Par Par_isRC  rrc_Par)). 
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc2  Par_Cat rc_Par Par_isRC  rrc_Par).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc3  Par_Cat rc_Par Par_isRC  rrc_Par).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc4  Par_Cat rc_Par Par_isRC  rrc_Par). *)

Definition rrc_in_CompN_all : @RangeComb CompsNR rc_CompN CompsNR.
eexists. Unshelve. Focus 5.
eexists; try auto. destruct a as [a]. destruct b as [b]. destruct X as [X].
simpl. simpl in X.  
 exact ( @rrc Par_isCRC rc_Par Par_isCRC rrc_Par _ _ X); try auto. simpl.
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g;
apply exist_eq; simpl; try (  apply (@rrc1  Par_Cat rc_Par Par_isRC  rrc_Par)). 
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc2  Par_Cat rc_Par Par_isRC  rrc_Par).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc3  Par_Cat rc_Par Par_isRC  rrc_Par).
intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl; simpl in f; try simpl in g.
apply exist_eq. simpl.  apply (@rrc4  Par_Cat rc_Par Par_isRC  rrc_Par). 
Defined.

Definition Range_CompN : @RangeCat CRC_CompN rcCompN CRC_CompN rrc_in_CompN.
exists. Defined.

Definition build1 : CRC_CompN.
exists (build_compsNR_obj 1). auto. Defined.

Definition nat_in_comp (x: nat) : proj1_sig (build_compsNR_obj 1).
simpl. exists; try exists. exact x. Defined.

Lemma rewrite_list1 : forall (x:nat) (tt : par_p_term), 
 (x :: nil) = (N_toProd (build_compsNR_obj 1) (x, tt)).
Admitted.

Lemma domain_compute : forall (f : Hom (build_compsNR_obj 1) (build_compsNR_obj 1)), forall (prf_f : prf) , 
forall (pf :  prf_par_map prf_f (build_compsNR_obj 1) =  (pr1f 1 1 f)), forall (x : nat) ,
 ((projT1 (proj1_sig (@rc CompNRC rc_CompN  _ _ f)) ) (nat_in_comp x)) <-> (exists y, converges_to prf_f (x :: nil) y).
simpl. unfold nat_in_comp. unfold prf_par_map.
simpl. intros. split. destruct f.
destruct x0. simpl. intros. 
unfold pr1f in pf. simpl in pf.
apply par_eqv_def in pf. simpl in pf.
destruct pf. destruct (H0 (x, tt)).
replace (x :: nil) with (N_toProd (build_compsNR_obj 1) (x, tt)).
exact (H3 H). rewrite (rewrite_list1 x tt). auto.
intro. destruct f. destruct x0. simpl.
unfold pr1f in pf. simpl in pf.
apply par_eqv_def in pf. simpl in pf.
destruct pf. destruct (H0 (x, tt)). apply H2.
rewrite (rewrite_list1 x tt) in H. auto.
Defined.

(*
Lemma domain_computable : forall (f : Hom (build_compsNR_obj 1) (build_compsNR_obj 1)), forall (prf_f : prf) , 
forall (pf :  prf_par_map prf_f (build_compsNR_obj 1) =  (pr1f 1 1 f)), forall (x : nat) ,
exists rc_prf, prf_par_map rc_prf (build_compsNR_obj 1) =  (pr1f 1 1 (@rc CompNRC rc_CompN  _ _ f)).
simpl. intros. generalize (domain_compute f). intro dcf.
destruct f. unfold prf_par_map. simpl. unfold prf_par_map in pf. 
apply par_eqv_def in pf. simpl in pf. destruct pf.
eexists. apply par_eqv_def. simpl. split.
simpl.  intro. split. intro.
Unshelve. Focus 4. 
 generalize (H z).
 ((projT1 (proj1_sig (@rc CompNRC rc_CompN  _ _ f)) ) (nat_in_comp x)) <-> (exists y, converges_to prf_f (x :: nil) y).
*)


Lemma range_compute : forall (f : Hom (build_compsNR_obj 1) (build_compsNR_obj 1)), forall (prf_f : prf) , 
forall (pf :  prf_par_map prf_f (build_compsNR_obj 1) =  (pr1f 1 1 f)), forall (y : nat) ,
 ((projT1 (proj1_sig (@rrc CompNRC rc_CompN CompNRC rrc_in_CompN_all  _ _ f)) ) (nat_in_comp y)) <-> 
  (exists x, converges_to prf_f (x :: nil) y).
simpl. unfold nat_in_comp. unfold prf_par_map.
simpl. intros. split. destruct f.
destruct x. simpl. intros. 
unfold pr1f in pf. simpl in pf.
apply par_eqv_def in pf. simpl in pf.
destruct pf. destruct H. destruct H.
destruct (H0 x0). generalize (H1 x0 (H3 x1) x1 (H3 x1)). intro.
generalize dependent H3. 
replace (N_toProd (build_compsNR_obj 1) x0) with ((fst x0 :: nil)) .
intros. rewrite H in H4.
exists (fst x0). simpl in H4. destruct (H3 x1).
rewrite <- H4. apply AC_rewrite.
rewrite (rewrite_list1 (fst x0) (snd x0)). simpl. auto.
intros. destruct f. destruct x. simpl.
unfold pr1f in pf. simpl in pf.
apply par_eqv_def in pf. simpl in pf.
destruct pf. destruct H.
exists (x0, tt). destruct (H0 (x0, tt)).
assert ((∃ y : nat, converges_to prf_f (N_toProd (build_compsNR_obj 1) (x0, tt)) y)).
exists y. replace (N_toProd (build_compsNR_obj 1) (x0, tt)) with (x0 :: nil).
auto. Focus 2.
generalize (H1 (x0, tt) H4 (H2 H4) H4). intro. simpl in H5.
exists (H2 H4). destruct (p (x0, tt) (H2 H4)) as [p1 p2].
assert (p2 = tt). destruct p2. auto. rewrite H6. simpl in H5.
rewrite <- H5. rewrite (unique_conv prf_f (x0 :: nil) y 
 (AC_select_y (N_toProd (build_compsNR_obj 1) (x0, tt)) prf_f H4)).
auto. auto. generalize dependent H4.
replace (N_toProd (build_compsNR_obj 1) (x0, tt)) with (x0 :: nil).
intros. exact  (AC_rewrite (x0 :: nil) prf_f H4).
rewrite (rewrite_list1 x0 tt). auto.
rewrite (rewrite_list1 x0 tt). auto.
Defined.
   

Definition rrc_one_in_CompN (f : @Hom CompsNR (build_compsNR_obj 1) (build_compsNR_obj 1)) (pf : conv_to_cat_prop _ _ f) : 
 { rf : @Hom CompsNR (build_compsNR_obj 1) (build_compsNR_obj 1) | conv_to_cat_prop _ _ rf}.
eexists. Unshelve. Focus 2. eexists; try auto.
eexists. Unshelve. Focus 2. intros.
destruct f. destruct x.
 exact (conv_to_cat_prop 1 1 f).
simpl. intros. exists; try exists. 
destruct f. destruct x0.

 destruct x. eexists. 
Unshelve. Focus 2. eexists; try auto. simpl.
eexists. Unshelve. Focus 2. intro.
simpl in pf. exact pf. simpl in x.
exact (x H). intros. simpl in H. destruct pf.
simpl in p. exact (p x0 H).
simpl. split. destruct pf.
 destruct e.
unfold prf_par_map. simpl. eexists. apply par_eqv_def.
simpl. 
unfold prf_par_map in H. apply par_eqv_def in H.
simpl in H. destruct H. exists. exact H. exact H0.
unfold prf_par_map. eexists. apply par_eqv_def.
simpl. split; intros. split; intros. destruct pf. 
destruct e. destruct c. Unshelve. (*
Focus 3. apply (unique_conv (Proj 1) (N_toProd (build_compsNR_obj 1) z)).
apply AC_rewrite. generalize (conv_proj' (N_toProd (build_compsNR_obj 1) z) 1).
simpl. destruct z as [z1 z2].
 replace ( (N_toProd (build_compsNR_obj 1) (z1,z2))) with (z1 :: nil).
assert (blt_nat (length (z1 :: nil)) 1 = false).
unfold blt_nat. simpl. auto. simpl. intro. exact (H1 eq_refl).
unfold N_toProd. simpl. 
 econstructor. inversion e. *)
apply par_eqv_def in e. simpl in H2. destruct H2.
 destruct (H0 z ). unfold prf_par_map in  e0. 
simpl in e0. apply par_eqv_def in e0. simpl in e0.
destruct e0 as [e01 e02]. destruct (e01 z) as [e01z].
destruct H4. split. try tauto.
destruct (e02 z) as [e02z].
destruct (e0 z). destruct (H3 H).
generalize (H2 z
inversion H1
generalize (H1 H).
inversion H2.
apply H1.
rewrite par_eqv_def in H
destruct H
Focus 2.
Focus 3. exact H0.
exists Sub Succ (x_out x') 0 0 x0. unfold prf_par_map. simpl.
apply par_eqv_def. simpl. split.


destruct pf. split.
destruct ( (build_compsNR_obj 1)).

Lemma dom_range_same (f : @Hom CompsNR (build_compsNR_obj 1) (build_compsNR_obj 1)) (pf : (conv_to_cat_prop 1 1 f)) : True.
unfold conv_to_cat_prop in pf. destruct f. simpl in pf. 
unfold prf_par_map in pf. simpl in pf. 
destruct x. destruct pf. destruct H. destruct H0.
apply par_eqv_def in H0. apply par_eqv_def in H.
simpl in H0. simpl in H.
simpl in H0.
undestruct N_obj.
destruct f. destruct x. destruct x0.
simpl in x. simpl in x0. simpl in c.
unfold Comp_mapsN in c. simpl in c. generalize dependent c.
replace (AC_select_Product x e) with 1 in c.
generalize dependent p. destruct N_obj.


(proj1_sig (@rrc CompNCRC rc_CompN CompNCRC CompNRangeComb a b f)) =
  (proj1_sig (@rc CompNCRC rc_CompN   a b f)).

 intros; try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
simpl; simpl in f; try simpl in g;
try apply exist_eq;
try destruct f as [f]; try destruct g as [g]; 
try destruct a as [a]; try destruct b as [b]; try destruct c as [c];
try destruct f as [f]; try destruct g as [g]; simpl.
destruct (rangeCompN _ _ _ ). apply exist_eq.
apply par_eqv_def. unfold HomParEqv; simpl.
destruct x. simpl. split. split. intro.
  (exist (λ x : obj, ∃ n : nat, x = nthProdC rc_Par nat n) a e)
  (exist (λ x : obj, ∃ n : nat, x = nthProdC rc_Par nat n) b e0)
  (exist (λ _ : hom a b, True) f t1)).
intros. destruct 




Instance Turing_CompN : TuringCat rcCompN N_obj.
exists. apply eq_charac. simpl.
exists bullet_CompN. intro.
eexists. Unshelve. Focus 3.
unfold Hom. simpl. eexists; try auto.
Unshelve. Focus 2. eexists; try auto. 
eexists. intros. Unshelve. Focus 2. intro. exact True.
destruct x. exists. destruct f.
unfold Comp_mapsN in c. destruct (re_build_obj (proj1_sig N_obj)).
simpl in c.
assert (∃ n : nat,
          par_p_prod (par_p_prod nat par_p_term) (par_p_prod nat par_p_term) =
          nthProdC rc_Par nat n). exists 2. simpl.
Focus 2. replace _ with H0 in c. replace _ with H0 in c.
 replace par_p_prod with RCat_HP. 
rewrite AnAm_Anm_pf. unfold par_p_prod.
compute. rewrite AnAm_Anm_pf.
forall pf,  (AC_select_Product (par_p_prod (par_p_prod nat par_p_term) (par_p_prod nat par_p_term)) pf) = 2).
Focus 2.  rewrite H0 in c.
 with 2 in c.
rewrite re_build_obj in c. simpl in c. destruct x.
destruct x. destruct c. compute in p.
Definition x0 : nat * unit * (nat * unit).
exists; exists; try exists.
 simpl. unfold TuringObj.
intros.


∃ h : Hom N_obj N_obj,
TotMaps rcCompN {|  |} N_obj N_obj h
∧ f = bullet_CompN ∘ pProd_morph_ex (RCat_HP N_obj N_obj) (h ∘ Pi_1p) Pi_2p

Fixpoint x_out (x : nat) : prf :=
match x with 
  | 0 => Zero
  | S x' => Sub Succ (x_out x') 0 0 
end.



Definition test_x_out : forall x ln, converges_to (x_out x) ln x.
intros. compute. induction x. econstructor. 
econstructor. 
exact IHx. econstructor.
Defined.

(*
Definition k_comb : prf :=  x_out ( enum_prf (Proj 1)). 

Lemma k_comb_lem : forall x z , converges_to k_comb (x :: nil) z -> 
   forall q, converges_to (nat_to_prf z) (q :: nil) q.
unfold k_comb. intros.
assert (converges_to (x_out (enum_prf (Proj 1))) (x :: nil) (enum_prf (Proj 1))). 
apply test_x_out. replace z with (enum_prf (Proj 1)).
rewrite prf_nat_prf. econstructor. simpl. auto. apply (unique_conv (x_out (enum_prf (Proj 1)))  (x :: nil)).
auto. auto.
Defined.
*)

(*
Lemma Leibnitz_Kleene : forall A B : Par_Cat , forall f g : Hom A B, (projT1 f = projT1 g -> False ) -> HomParEqv A B f g -> 
(projT1 f = projT1 g). intros a b f g. rewrite par_eqv_def.
intros. rewrite H0.  unfold HomParEqv in H. inversion H.
Hom A B = {
  <-> (forall (P : (Hom A B) -> Prop), P f <-> P g).
intros. destruct f as [fp f]; destruct g as [gp g].
simpl. split. intros. split; intros. destruct H.
*)

Definition k_comb : prf := Sub (Proj 1) (Proj 1) 0 1. 
 
Lemma k_comb_lem : forall x y p1 , converges_to (nat_to_prf (AC_select_y (x :: nil) k_comb p1) )  (y :: nil) x.
intros. compute in p1. destruct p1. apply (conv_sub' 0 1  in c.
generalize (conv_sub' (x :: nil) (Proj 1) (Proj 1) 0 1 ).

 AC_select_y (y :: nil) (nat_to_prf (AC_select_y (x :: nil) k_comb p1)) p2 = x.
intros. destruct p2. unfold k_comb. 
generalize (AC_rewrite (y :: nil) (nat_to_prf
       (AC_select_y (x :: nil)
          (Sub (Proj 1) (Proj 1) 0 1) p1)) (ex_intro (λ y0 : nat, converges_to (nat_to_prf
             (AC_select_y (x :: nil) (Sub (Proj 1) (Proj 1) 0 1) p1))  (y :: nil) y0) x0 c) ).
intro. 

 | conv_sub' : forall (l : list nat), forall (f g : prf), forall (n m x y : nat), converges_to g l x ->
    converges_to f (pcombine n m l x) y ->
       converges_to (Sub f g n m) l y



Lemma bullet_computable : forall (n m : nat) (f : @Hom Par_isCRC (@nthProdC Par_isCRC rc_Par Par_isCRC Par_isCRC  nat n) 
  (@nthProdC Par_isCRC rc_Par Par_isCRC Par_isCRC  nat m)), 
    (@isAppStructFornProd Par_isCRC rc_Par Par_isCRC Par_isCRC nat bullet_CompN n m f).
 apply k_s_comb_comp_allP. 
unfold has_k_s. unfold bullet_CompN. simpl. split. Focus 2.
eexists. intros. Unshelve. Focus 2.
eexists. Unshelve.
Focus 2. unfold Hom. simpl. eexists.
Unshelve. Focus 2. intro. exact True. intros.
exact (enum_prf k_comb). simpl. unfold Id. auto.
 intros. unfold Compose. unfold par_p_prod.
simpl. destruct x as [x]; destruct y as [y].
unfold par_pProd_morph_ex. simpl.
destruct x as [x]; destruct y as [y].
simpl. apply par_eqv_def. unfold HomParEqv. 
 split; try intros; try split; try split; try intros; try split; try split; try split; try auto ;
 try auto; try intros; try split; try inversion e1; try inversion e0; try inversion e; try auto.
destruct p. simpl.
rewrite prf_nat_prf. unfold k_comb. 
exists (enum_prf (Proj 1)). apply test_x_out.
destruct p. destruct a. destruct a. simpl.
generalize (e1 (conj t x0)). simpl. rewrite prf_nat_prf.
intro. exists (n0 z y0).
generalize (fun g gp => k_comb_lem g (AC_select_y (n z x0 :: nil) k_comb e2) gp (n0 z y0)).
intro. generalize (AC_rewrite (n z x0 :: nil) k_comb e2). intro.
 apply ( H0 (n z x0) H5).
destruct pf. destruct a. destruct a. destruct a. simpl.
generalize (e1 (conj (conj (conj t x0) e2) y0)). simpl. 
generalize (e2 (conj t x0)). simpl. rewrite prf_nat_prf. intros.
apply (unique_conv (nat_to_prf (AC_select_y (n z x0 :: nil) k_comb e3)) (n0 z y0 :: nil)).
generalize (AC_rewrite (n0 z y0 :: nil) (nat_to_prf (AC_select_y (n z x0 :: nil) k_comb e3)) e4). auto.
replace (n z pf1) with (n z x0). unfold k_comb.
replace (AC_select_y (n z x0 :: nil) (x_out (enum_prf (Proj 1))) e3) with
  (enum_prf (Proj 1)).
generalize unique_conv.
assert (∃ y1 : nat, converges_to (x_out (enum_prf (Proj 1))) (n0 z y0 :: nil) y1).
exists (enum_prf (Proj 1)). apply test_x_out.
assert ( (AC_select_y (n0 z y0 :: nil)
          (x_out (enum_prf (Proj 1))) H0) = ( (enum_prf (Proj 1)))).
apply (unique_conv (x_out (enum_prf (Proj 1))) (n z x0 :: nil)). Focus 2.
apply test_x_out. Focus 2. intros. rewrite H5.
generalize (unique_conv (x_out (enum_prf (Proj 1))) (n z x0 :: nil) ( (enum_prf (Proj 1)))  (AC_select_y (n z x0 :: nil) (x_out (enum_prf (Proj 1))) e3)).
intros.
apply test_x_out.
apply (k_comb_lem   
generalize (AC_rewrite (n0 z y0 :: nil) (nat_to_prf (AC_select_y (n z x0 :: nil) k_comb e3)) (n z pf1)).
 auto.

intro.
(n z x0) (AC_select_y (n z x0 :: nil) k_comb e2) 
destruct e2.
Lemma k_comb_lem : forall x z , converges_to k_comb (x :: nil) z -> 
   forall q, converges_to (nat_to_prf z) (q :: nil) q.

exists (n0 z y0). simpl.
generalize (fun p => k_comb_lem ( enum_prf (Proj 1)) (AC_select_y (n z x0 :: nil) 
        (nat_to_prf (enum_prf k_comb)) 
        (e1 (conj t x0))) p (n0 z y0)).  intro.
apply H0. unfold k_comb.
generalize (test_x_out (enum_prf (Proj 1)) (enum_prf (Proj 1) :: nil)).
intro. 
generalize (AC_rewrite (n z x0 :: nil) (nat_to_prf (enum_prf (x_out (enum_prf (Proj 1))))) (e1 (conj t x0)) ).
generalize dependent prf_nat_prf; generalize dependent (e1 (conj t x0)). simpl.
intros.
rewrite prf_nat_prf.
intro.
assert ((AC_select_y (n z x0 :: nil) 
     (nat_to_prf (enum_prf (x_out (enum_prf (Proj 1))))) 
     (e1 (conj t x0))) = (enum_prf (Proj 1))).
rewrite (unique_conv (x_out (enum_prf (Proj 1))) (enum_prf (Proj 1) :: nil) (enum_prf (Proj 1)) (AC_select_y (n z x0 :: nil) 
  (nat_to_prf (enum_prf (x_out (enum_prf (Proj 1))))) 
  (e1 (conj t x0))) H5). auto.
forall f ln y z, converges_to f ln y -> converges_to f ln z -> y=z.
Admitted.
generalize (AC_rewrite (enum_prf (Proj 1) :: nil) (x_out (enum_prf (Proj 1))) ).
intro. assert (∃ y : nat, converges_to (x_out (enum_prf (Proj 1))) (enum_prf (Proj 1) :: nil) y).
exists ( (enum_prf (Proj 1))). apply test_x_out. 
replace ((AC_select_y (n z x0 :: nil) (nat_to_prf (enum_prf (x_out (enum_prf (Proj 1)))))
     (e1 (conj t x0)))) with  (AC_select_y (enum_prf (Proj 1) :: nil)
          (x_out (enum_prf (Proj 1))) H7). exact (H6 H7). 
assert ((nat_to_prf
     (enum_prf (x_out (enum_prf (Proj 1))))) = (x_out (enum_prf (Proj 1)) )). rewrite prf_nat_prf. auto.
assert (converges_to (nat_to_prf
     (enum_prf (x_out (enum_prf (Proj 1))))) 
apply unique_conv.
apply pf_ir.
generalize dependent (H6 H7).
generalize H7.
destruct (e1 (conj t x0)) as [yy1 yy2].
exists yy1. unfold k_comb in yy2.
generalize yy2. intro yy3. rewrite prf_nat_prf in yy3.

replace (x_out (enum_prf (Proj 1))) with (nat_to_prf (enum_prf (x_out (enum_prf (Proj 1))))) in H6.
apply H6. (e1 (conj t x0))).
 ).

rewrite prf_nat_prf.
 apply k_comb_lem.
 exists (enum_prf (x_out (enum_prf (Proj 1)))). 
rewrite prf_nat_prf. apply test_x_out.
assert (blt_nat (length ((enum_prf (x_out (enum_prf (Proj 1)))) :: nil)) 1 = false). unfold blt_nat. simpl. auto.
generalize (conv_proj' ((enum_prf (x_out (enum_prf (Proj 1)))) :: nil) 1 H0). simpl.
rewrite prf_nat_prf. intros. apply test_x_out. unfold x_out
 auto. simpl. destruct p. destruct a.
destruct a. exists (n0 z y0). 
assert (blt_nat (length (n z x0 :: nil)) 1 = false). unfold blt_nat. simpl. auto.
generalize (conv_proj' (n z x0 :: nil) 1 H0). 
assert (nat_to_prf (enum_prf (Proj 1)) = Proj 1). rewrite prf_nat_prf. auto.
simpl. intro. Check e1. rewrite H5.
 replace (nat_to_prf (enum_prf (Proj 1))) with (Proj 1).
assert ((AC_select_y (n z x0 :: nil) (nat_to_prf (enum_prf (Proj 1))) (e1 (conj t x0))) = ).
assert (exists y1, converges_to (Proj 1) (n z y :: nil) y1).
exists  (n z x0). exact H6. auto.
generalize (AC_rewrite (n0 z y0 :: nil) (Proj 1)). elim H5.
split;  try inversion e1; try auto. inversion e. auto.
intros.  inversion e1.

(k . x) . y)
x
destruct x as [x]; destruct y as [y]; destruct z as [z].