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
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Init.Nat.

Generalizable All Variables. 

Fixpoint leq (n m : nat) : Prop :=
  match n, m with
    | 0, _ => True
    | _, 0 => False
    | S n', S m' => leq n' m'
  end.


(* bullet map application *)
Definition bulletn_once `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : RC) (n : nat) (bullet : Hom (RCat_HP A A) A) : 
Hom ( RCat_HP A (nthProdC rc A (S n))) ( RCat_HP A (nthProdC rc A n)) .
Proof.
 exact (pProd_morph_ex (RCat_HP A (nthProdC rc A (S n))) (bullet  ∘(pProd_morph_ex (RCat_HP A (nthProdC rc A (S n))) 
    (Pi_1p) ((projto_2ndA A n) ∘Pi_2p) ))
  (projto_restAs A n)).
Defined.


(* n-fold application of bullet *)
Fixpoint bullet_n `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n : nat) (bullet : Hom (RCat_HP A A) A) : Hom ( RCat_HP A (nthProdC rc A n)) A  := 
match n with
  | 0 => bullet ∘(pProd_morph_ex A (id A) (id A)) ∘Pi_1p
  | S 0 => Pi_1p ∘ (bulletn_once  A 0 bullet)
  | S (S m') => (bullet_n A  (S m') bullet ) ∘(bulletn_once  A  (S m') bullet)
end.

(*
(* 1 x A^n product  *)
Fixpoint x1nthProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} ( RCat_term : ParTerm ) (RCat_HP : Has_pProducts )
(A : RC) (n : nat) : RC  := 
match n with

  | 0 => RCat_term
  | S 0 => A
  | S m => (RCat_HP A (nthProd rc RCat_term RCat_HP A m))

end. *)

Open Scope list_scope.
Open Scope nat_scope.



(*
(* n-fold product of maps A^n -> A *)
Fixpoint pProd_morph_ex_n `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n : nat)  (lf : list (Hom (nthProdC rc A n) A))  :
     Hom (nthProdC rc A n) (nthProdC rc A (length lf))  := 
match lf with
  | nil => (pt_morph (nthProdC rc A n))
  | f :: nil => f
  | f :: lf' => (pProd_morph_ex (nthProdC rc A n) f (pProd_morph_ex_n A n lf' ))
end.


(* n+1 - fold product of maps 1xA^n -> A *)
Definition pProd_morph_ex_1xn `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
 (A : Obj) (n : nat)  (lf : list (Hom (nthProdC rc A n) A)) (f_t : Hom (nthProdC rc A n) RCat_term) :
     Hom (nthProdC rc A n) (RCat_HP RCat_term (nthProdC rc A (length lf)) ) := (pProd_morph_ex (nthProdC rc A n) f_t (pProd_morph_ex_n A n lf)).

*)

(* True when a map f : A^n -> A is computable *)
Definition f_comp `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) (n : nat) (f : Hom (nthProdC rco A n) A) : Prop := 
  exists (p : @point CRC rco CRC CRC A), ((f = (bullet_n A n bullet)    ∘(@pProd_morph_ex CRC rco CRC A (nthProdC rco A n) (@RCat_HP CRC rco CRC CRC A (nthProdC rco A n)) _
    ((proj1_sig p) ∘((@pt_morph CRC rco CRC (@RCat_term CRC rco CRC CRC) (nthProdC rco A n)) )) (id (nthProdC rco A n))) )      /\
      ((leq (S (S 0)) n)  -> ((rc _ _ (compose _ _ _ _ (@pProd_morph_ex CRC rco CRC A (nthProdC rco A (n - 1))
                 (@RCat_HP CRC rco CRC CRC A (nthProdC rco A (n - 1))) 
      (nthProdC rco A (n - 1))
     ((proj1_sig p) ∘ (@pt_morph CRC rco CRC (@RCat_term CRC rco CRC CRC) (nthProdC rco A (n - 1)))) (id (nthProdC rco A (n - 1))  ))   (bullet_n A (n - 1) bullet)  ) )      
        = (id (nthProdC rco A (n - 1))  )))).

(* True when a map f_t : A^n -> 1 is computable *)
Definition isAppStructTerm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC)(bullet : Hom (RCat_HP A A) A) 
 (n : nat) (f_t : Hom (nthProdC rco A n) (nthProdC rco A 0)) : Prop.
  generalize(f_comp A bullet n). 
  destruct n. intro. 
  exact (exists (p  : @point CRC rco CRC CRC A), compose _ _ _ _ (pProd_morph_ex _ (proj1_sig p) (pt_morph _ ) )
  (compose _ _ _ _ 
    (bullet_n A 0 bullet) (@pt_morph CRC rco CRC (@RCat_term CRC rco CRC CRC) A)) = f_t ).
  simpl in f_t. simpl.
   intro f_comp. exact (f_comp (Pi_1p ∘ (rc _ _ f_t))). 
Defined.

 
(* True when (A, bullet) to be an applicative structure, shown for each n *)
Fixpoint isAppStructFornList `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  (n : nat) (lf : list (Hom (nthProdC rco A n) A)) (f_t : Hom (nthProdC rco A n) RCat_term) : Prop :=
match lf with
  | nil => (isAppStructTerm A bullet n f_t)
  | f :: nil => (f_comp A bullet n f)
  | f :: lf' => (f_comp A bullet n f) /\ (isAppStructFornList A bullet n lf' f_t )
end.

(*
Definition nthP_toP  `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (object : nth_ProdT rco) : ParProd A (nth_ProdT rco).
*)

(* True when (A, bullet) to be an applicative structure, shown for each n *)
Definition  isAppStructFornProd_test_m `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  (n m : nat) (f :  (Hom (nthProdC rco A n) (nthProdC rco A m)))  
(test_prop : ∀ 
   (A : CRC), Hom (RCat_HP A A) A → ∀ n m : nat, Hom (nthProdC rco A n) (nthProdC rco A m) -> Prop) : Prop.
destruct m. exact (isAppStructTerm A bullet n f). exact 
((test_prop A bullet n m (compose _ _ _ _ f Pi_2p  )) /\
  (f_comp A bullet n (compose _ _ _ _ f Pi_1p ) )). Defined. 


Fixpoint   isAppStructFornProd `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  (n m : nat) (f :  (Hom (nthProdC rco A n) (nthProdC rco A m)))  : Prop :=
match m with
  | 0 => (isAppStructFornProd_test_m  A bullet n m f (isAppStructFornProd) )
  | S m' => (isAppStructFornProd_test_m  A bullet n m f (isAppStructFornProd) )
end.

(*
Definition id_comp `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) 
  (n m : nat) (f :  (Hom (nthProdC rco A n) (nthProdC rco A m)))


(isAppStructTerm A bullet n f)
(f_comp A bullet n (compose _ _ _ _ f Pi_1p ) ) /\ (isAppStructFornProd A bullet n m' (Pi_2pn _ _ _ m' f ))
(@Pi_2p CRC rc CRC
*)

(*
(*
Definition map_n_m `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`(CRC : @CartRestrictionCat C rco RC) (A : CRC) (n m : nat) : Type.
exact (Hom (nthProdC rco A n) (nthProdC rco A (S (S m)))). Defined.


Definition nPi_2 `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (f :  (Hom (nthProdC rco A n) (nthProdC rco A m)))  : Hom (nthProdC rco A n) (nthProdC rco A (m-1)).
destruct m. simpl. exact f.
unfold nthProdC. replace (S m - 1) with m. destruct m. unfold nthProd. exact (pt_morph _).
unfold nthProd. unfold nthProdC in f. unfold nthProd in f. simpl in f.
exact (compose _ _ _ _ f Pi_2p). compute. destruct m. auto. auto. Defined. 


Definition map_n_A `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`(CRC : @CartRestrictionCat C rco RC) (A : CRC) (n : nat) : Type.
exact (Hom (nthProdC rco A n) A). Defined.

Definition PrCo  `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`(CRC : @CartRestrictionCat C rco RC) : forall (A : CRC) (n m : nat), forall (f :  map_n_m),
Hom (nthProdC rco A n) (RCat_HP A (nthProdC rco A (S m))). intros A n m f.
simpl. unfold nthProdC. unfold nthProd. simpl. simpl in f. exact f. Defined.

Definition fPi_1pn `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) : map_n_m ->
 (Hom (nthProdC rco A n) A). 
unfold nthProdC; unfold nthProd.
destruct m. destruct n. simpl. *)

(*
Definition fPi_1pn `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m m': nat) : (Hom (nthProdC rco A n) (nthProdC rco A m)) ->
(list (Hom (nthProdC rco A n)  (nthProdC rco A m')).
destruct m. simpl. exact f. replace (S m - 1) with m.
unfold nthProdC. unfold nthProdC in f. destruct m.
unfold nthProd in f. simpl in f.
Check (compose _ _ _ _  f (@Pi_2p _ _ _ A)).
exact (compose _ _ _ _  f (@Pi_2p _ _ _ A _  _)).
destruct (nthProdC rco A m).
compute in f_t. exact f_t. Defined.  

Coercion PrCo . `(A : CRC) `(n m : nat) Type >-> Type.  (Hom (nthProdC rco A n) (nthProdC rco A (S (S m)))) >->
Hom (nthProdC rco A n) (RCat_HP A (nthProdC rco A (S m))).

Definition coer `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n : nat) (f_t : Hom (nthProdC rco A n) (nthProdC rco A 0)) :
Hom (nthProdC rco A n) RCat_term. simpl in f_t. exact f_t. Defined. 



*)

Definition SSmpr_map `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) : (Hom (nthProdC rco A n) (nthProdC rco A (S (S m)))) ->
Hom (nthProdC rco A n) (RCat_HP A (nthProdC rco A (S m))).
unfold nthProdC. unfold nthProd. intro f. exact f. Defined.


Definition Apr_map `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) : (Hom (nthProdC rco A n) (nthProdC rco A (S m))) -> (Hom (nthProdC rco A n) A).
unfold nthProdC. unfold nthProd. destruct m. intro f. exact f. intro f.
exact (compose _ _ _ _ f Pi_1p ). Defined. 

(*
Hom (nthProdC rco A n) (nthProdC rco A (S m))
Hom (nthProdC rco A n) (nthProdC rco A (S (S m'))) *)

Definition istSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (f : Hom (nthProdC rco A n) (nthProdC rco A  (S m))) : 
{m : nat & 
 Hom 
 (nthProdC rco A n)
 (nthProdC rco A (S (S m)))}.
destruct m. exists 0. 
unfold nthProdC. unfold nthProd. simpl.
unfold nthProdC in f. unfold nthProd in f. simpl in f.
exact (pProd_morph_ex _ f f).
exists m. exact f.
Defined.



Definition nthProdisProd `{C : Category} `(rc : @RestrictionComb C) `{RC : @RestrictionCat C rc} `{CRC : @CartRestrictionCat C rc RC} 
(A : CRC) (n : nat) : ParProd A (nthProdC rc A n).
assert ((ParProd A (nthProdC rc A n)) = (nthProdC rc A (S n))).
unfold nthProdC. unfold nthProd. assert ( (ParProd A
  ((fix
    nthProd 
    (C0 : Category) 
    (rc0 : RestrictionComb C0) 
    (RC0 : RestrictionCat C0 rc0) 
    (RCat_term : ParTerm) 
    (RCat_HP : Has_pProducts) 
    (A0 : RC0) 
    (n0 : nat) {struct n0} : RC0 :=
      match n0 with
      | 0 => p_term
      | 1 => A0
      | S (S _ as m) => p_prod
      end) C rc CRC RCat_term RCat_HP A n))
 =   (nthProdC rc A (S n))).

Instance nthProdisTerm `{ RC: RestrictionCat  }  : Category := C.

Coercion nthProdisProd : CRC >-> ParProd.  

Definition nPi_1 `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n : nat) : Hom (nthProdC rco A n) (nthProdC rco A (n-1)).

Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (f : Hom (nthProdC rco A n) (nthProdC rco A (S (S m))))
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match m with 
  | 0 =>  ( ( (compose _ _ _ _ (SSmpr_map A n m f) Pi_1p) ):: 
          (Apr_map A n m (compose _ _ _ _ (SSmpr_map  A n m f) Pi_2p) ) :: nil, pt_morph _ )
  | S m' => ( (compose _ _ _ _  (SSmpr_map A n m f) (@Pi_1p _ _ _ A _ _)) 
          :: fst (MapToListSSm  A n  (S m) (projT2  (istSSm A n m (compose _ _ _ _  (SSmpr_map A n _ f)  Pi_2p) )) ),
         pt_morph _) 
end. 

(projT1  (istSSm A n m (compose _ _ _ _  (SSmpr_map A n _ f)  Pi_2p) ))

Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n c : nat) (f : {m : nat & Hom (nthProdC rco A n) (nthProdC rco A (S (S m))) })
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match c with 
| 0 => (nil, pt_morph _ )
| S c' => 
  match (projT1 f) with 
     | 0 =>  ( ( (compose _ _ _ _ (SSmpr_map A n (projT1 f) (projT2 f)) Pi_1p) ):: 
           (Apr_map A n (projT1 f)  (compose _ _ _ _ (SSmpr_map  A n (projT1 f) (projT2 f)) Pi_2p) ) :: nil, pt_morph _ )
     | S m' => ((compose _ _ _ _  (SSmpr_map A n (projT1 f) (projT2 f)) (@Pi_1p _ _ _ A _ _)) 
             :: fst (MapToListSSm  A n c'  (istSSm A n (projT1 f) (compose _ _ _ _  (SSmpr_map A n _ (projT2 f))  Pi_2p) ))  ,
           pt_morph _) 
  end
end.

Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n c : nat) (f : {m : nat & Hom (nthProdC rco A n) (nthProdC rco A (S (S m))) })
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match c with 
| 0 => (nil, pt_morph _ )
| S c' => 
  match (projT1 f) with 
     | 0 =>  ( ( (compose _ _ _ _ (SSmpr_map A n (projT1 f) (projT2 f)) Pi_1p) ):: 
           (Apr_map A n (projT1 f)  (compose _ _ _ _ (SSmpr_map  A n (projT1 f) (projT2 f)) Pi_2p) ) :: nil, pt_morph _ )
     | S m' => ((compose _ _ _ _  (SSmpr_map A n (projT1 f) (projT2 f)) (@Pi_1p _ _ _ A _ _)) 
             :: fst (MapToListSSm  A n c'  (istSSm A n (projT1 f) (compose _ _ _ _  (SSmpr_map A n _ (projT2 f))  Pi_2p) ))  ,
           pt_morph _) 
  end
end.


Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n c : nat) (f : {m : nat & Hom (nthProdC rco A n) (nthProdC rco A (S (S m))) })
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match c with 
| 0 => (nil, pt_morph _ )
| S c' => 
  match (S (S (projT1 f))) with 
     | 0 => (nil, pt_morph _ )
     | S 0 => (nil, pt_morph _ )
     | (S (S 0)) =>  ( ( (compose _ _ _ _ (SSmpr_map A n (projT1 f) (projT2 f)) Pi_1p) ):: 
           (Apr_map A n (projT1 f)  (compose _ _ _ _ (SSmpr_map  A n (projT1 f) (projT2 f)) Pi_2p) ) :: nil, pt_morph _ )
     | (S (S (S m'))) => ((compose _ _ _ _  (SSmpr_map A n (projT1 f) (projT2 f)) (@Pi_1p _ _ _ A _ _)) 
             :: fst (MapToListSSm  A n c'  (istSSm A n (projT1 f) (compose _ _ _ _  (SSmpr_map A n _ (projT2 f))  Pi_2p) ))  ,
           pt_morph _) 
  end 
end.

Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (f : Hom (nthProdC rco A n) (nthProdC rco A (S (S m))))
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match (S (S m)) with 
  | 0 => (nil, pt_morph _ )
  | S 0 => (nil, pt_morph _ )
  | (S (S 0)) =>  ( ( (compose _ _ _ _ (SSmpr_map A n m f) Pi_1p) ):: 
          (Apr_map A n m (compose _ _ _ _ (SSmpr_map  A n m f) Pi_2p) ) :: nil, pt_morph _ )
  | (S (S (S m'))) => (compose _ _ _ _  (SSmpr_map A n m f) (@Pi_1p _ _ _ A _ _)) 
          :: fst (MapToListSSm  A n  (projT1  (istSSm A n m (compose _ _ _ _  (SSmpr_map A n _ f)  Pi_2p) )) (projT2  (istSSm A n m (compose _ _ _ _  (SSmpr_map A n _ f)  Pi_2p) )) ,
         pt_morph _) 
end.

Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n : nat) (f : {m : nat & Hom (nthProdC rco A n) (nthProdC rco A (S (S m)))})
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match (S (S (projT1 f))) with 
  | 0 => (nil, pt_morph _ )
  | S 0 => (nil, pt_morph _ )
  | (S (S 0)) =>  ( ( (compose _ _ _ _ (SSmpr_map A n  (projT1 f) (projT2 f)) Pi_1p) ):: 
          (Apr_map A n  (projT1 f) (compose _ _ _ _ (SSmpr_map  A n  (projT1 f) (projT2 f)) Pi_2p) ) :: nil, pt_morph _ )
  | (S (S (S m'))) => ((compose _ _ _ _  (SSmpr_map A n  (projT1 f) (projT2 f)) (@Pi_1p _ _ _ A _ _)) 
          ::  fst (MapToListSSm  A n (existT
           (λ  m : nat, Hom (nthProdC rco A n) (nthProdC rco A (S (S m))))
           (S (projT1 f)) (compose _ _ _ _  (SSmpr_map A n _ (projT2 f))  Pi_2p) )) ,
         pt_morph _) 
end.


Fixpoint MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) f : Hom (nthProdC rco A n) (nthProdC rco A (S (S m))))
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match (S (S m)) with 
  | 0 => (nil, pt_morph _ )
  | S 0 => (nil, pt_morph _ )
  | (S (S 0)) =>  ( ( (compose _ _ _ _ (SSmpr_map A n m f) Pi_1p) ):: 
          (Apr_map A n m (compose _ _ _ _ (SSmpr_map  A n m f) Pi_2p) ) :: nil, pt_morph _ )
  | (S (S (S m'))) => ((compose _ _ _ _  (SSmpr_map A n m f) (@Pi_1p _ _ _ A _ _)) 
          :: fst (MapToListSSm  A n  m  (compose _ _ _ _  (SSmpr_map A n _ f)  Pi_2p) ) ,
         pt_morph _) 
end.

Apr_map A n m
MapToList _ _ _ _ A n m'  (compose _ _ _ _  (SSmpr_map A n m f)  (Pi_2p _ _ _ A _ _))
(*
Definition MapToListSSm `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (f : Hom (nthProdC rco A n) (nthProdC rco A (S (S m)))
  : ( list (Hom (nthProdC rco A n) A))*( Hom (nthProdC rco A n) RCat_term)
 :=
match m with 
  | 0 => (nil , (coer _ _ _ ))
  
*)

*)

Definition isAppStructForn `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (n m : nat) (bullet : Hom (RCat_HP A A) A) 
 (f : Hom (nthProdC rco A n) (nthProdC rco A m))
 := isAppStructFornProd A bullet n m f .




(* True when applicative system (A, bullet) is combinatory complete *)
Definition AppSysIsCombComp `{C : Category} `{rc : @RestrictionComb C} `{RC : @RestrictionCat C rc} 
`{CRC : @CartRestrictionCat C rc RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) : Prop := 
forall (n m : nat) (f : Hom (nthProdC rc A n) (nthProdC rc A m)),
   isAppStructForn A n m bullet f.

(* True when applicative system (A, bullet) has combinators k and s *)
Definition has_k_s `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC} (A : CRC) (bullet : Hom (RCat_HP A A) A) : Prop.
 exact ( (exists (s : @point CRC rco CRC CRC A), forall (x y z : @point CRC rco CRC CRC A) ,
  (compose _ _ _ _ 
  (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (compose _ _ _ _ 
    (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (compose _ _ _ _ 
    (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (proj1_sig s) (proj1_sig x)) 
  bullet) (proj1_sig y)) 
  bullet)  (proj1_sig z))  
      bullet ) = (compose _ _ _ _ (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (compose _ _ _ _ 
    (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (proj1_sig x) (proj1_sig z)) bullet ) (compose _ _ _ _ 
    (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (proj1_sig y) (proj1_sig z)) bullet ))  
      bullet )) /\
  (exists (k : @point CRC rco CRC CRC A), forall (x y : @point CRC rco CRC CRC A) ,
  (compose _ _ _ _ (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (compose _ _ _ _ 
    (@pProd_morph_ex CRC rco CRC A A (RCat_HP A A) _ (proj1_sig k) (proj1_sig x)) bullet ) (proj1_sig y))  
      bullet ) = (proj1_sig x))).
Defined.


(* (A, bullet) is combinatory complete whenever it has combinators k and s *)
Definition k_s_comb_comp_allP `{C : Category} `{rco : @RestrictionComb C} `{RC : @RestrictionCat C rco} 
`{CRC : @CartRestrictionCat C rco RC}  (A : CRC) : forall (bullet : Hom (RCat_HP A A) A),
   has_k_s A bullet <-> AppSysIsCombComp A bullet.
Proof.
  unfold AppSysIsCombComp. unfold has_k_s. 

Admitted. (*
compute.
  generalize dependent (RCat_HP A A).
 destruct (RCat_HP A A) as [AxA]. 
  destruct RC; destruct CRC; destruct rc; destruct C; destruct RCat_RC; destruct RCat_term. 
  elim bullet. destruct (RCat_HP A A) as [AxA]. 
  unfold has_k_s. split. compute. unfold AppSysIsCombComp in H.
  
generalize dependent H; generalize dependent bullet.
   
  destruct RCat_HP.

  eexists. intros. destruct x as [x]; destruct y as [y] ; destruct z as [z]. 
  destruct ?s. simpl. 
Check (compose p_term (RCat_HP A A) A
  (pProd_morph_ex p_term
     (compose p_term (RCat_HP A A) A (pProd_morph_ex p_term x z)
        bullet)
     (compose p_term (RCat_HP A A) A (pProd_morph_ex p_term y z)
        bullet)) bullet).
destruct (H.
 intro. 
  eexists. intros.

simpl. destruct RCat_RC. 
compute. *)





