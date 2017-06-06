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
Require Import Turing.

Generalizable All Variables. 


(* Type of a range combinator *)
Definition rrcType `(RC : RestrictionCat) : Type.
Proof.
  exact (forall a b : C, Hom a b -> Hom b b ).
Defined.


(* open maps *)
Definition Op `{RC : RestrictionCat} (a : RC) :=
  { e : Hom a a | rc a a e = e}.

(* Op(a) is a poset for any object a, with the following ordering *)
Definition Op_par_leq `{RC : RestrictionCat}  (a : RC) (e1 e2 : Op a) : Prop 
  := (proj1_sig e1) ∘ (proj1_sig e2) = (proj1_sig e1).

(* define the f* map *)
Definition f_star `{RC : RestrictionCat} (a b : RC) (f : Hom a b) : (Op b) -> (Op a).
  intro e. destruct RC. assert (RCat_RC = rc0). auto.
  exists (rc a b ((proj1_sig e) ∘ f)). rewrite H. 
  destruct e. simpl. rewrite H in rc_d. 
  compute in rc_d. destruct C. simpl. destruct rc0. simpl.
  replace (rc a a (rc a b (compose a b b f x))) 
    with (rc a a (compose _ _ _ (id a) (rc a b (compose a b b f x)))).
  rewrite <- (rc_d _ _ _ (id a) (compose a b b f x)).
  rewrite id_unit_right. auto. 
  rewrite (id_unit_right _ _ (rc a b (compose a b b f x))). auto.
Defined.

(* note that the e/\e' operation is simply e ∘ e *)
Definition op_wedge `{RC : RestrictionCat} (a : RC) : (Op a) -> (Op a) -> (Op a).
  intros e e'. destruct e; destruct e'. exists (x ∘ x0).
  destruct C. destruct RC.
  replace RCat_RC with rc0 in rc_d.
  destruct rc0. simpl. simpl in rc3. 
  simpl in e; simpl in e0.
  replace (rc a a (compose a a a x0 x)) with (rc a a (compose a a a (rc _ _ x0) x)).
  rewrite (rc3 _ _ _ x0 x). rewrite e. rewrite e0. auto. rewrite e0. auto. auto.
Defined.


(* open map definition in a restriction cateogry *)
Definition open_exist_f `{RC : RestrictionCat} (a b : RC) (f : Hom a b) (exist_f : (Op a) -> (Op b)) : Prop := 
    (forall e' : (Op b), Op_par_leq _ (exist_f (f_star _ _ f e')) e' ) /\
    (forall e : (Op a), forall e' : (Op b), Op_par_leq _ (op_wedge _ e (f_star _ _ f e')) (f_star _ _ f (op_wedge _ (exist_f e) e'))) /\
    (forall e : (Op a), forall e' : (Op b), Op_par_leq _ (op_wedge _ e' (exist_f e)) (exist_f (op_wedge _ (f_star _ _ f e') e) ) ).


(* open map definition in a restriction cateogry *)
Definition open `{RC : RestrictionCat} (a b : RC) (f : Hom a b) :=
exists ( exist_f : (Op a) -> (Op b)), open_exist_f a b f exist_f.


(* composition of open maps is open *)
Lemma composition_open `{RC : RestrictionCat} (a b c : RC) (f : Hom a b) (g : Hom b c) (pf : open _ _ f) (pg : open _ _ g) : open _ _ (g ∘ f).
Proof.
Admitted.

(* composition of open maps is open - specific exist_f version *)
Lemma composition_open_mapex `{RC : RestrictionCat} (a b c : RC) (f : Hom a b) (g : Hom b c) 
( exist_f : (Op a) -> (Op b)) ( exist_g : (Op b) -> (Op c))
(pf : open_exist_f a b f exist_f) (pg : open_exist_f b c g exist_g) :  
    open_exist_f a c (g ∘ f) (fun x =>  (exist_g (exist_f x))) .
Proof.
Admitted.


(* Range Combinator definition *)
Class RangeComb `{RC : RestrictionCat} : Type :=
{

    rrc : rrcType RC
  ; rrc1             : forall (a b : Obj), forall (f : Hom a b), rc b b (rrc a b f) = rrc _ _ f 
  ; rrc2             : forall (a b : Obj), forall (f : Hom a b), (rrc a b f) ∘ f = f 
  ; rrc3             : forall (a b c: Obj), forall (f : Hom a b)`(g : Hom b c), rrc _ _ ((rc _ _ g ) ∘ f) = (rc _ _ g) ∘ (rrc _ _ f)
  ; rrc4             : forall (a b c: Obj), forall (f : Hom a b)`(g : Hom b c), rrc _ _ (g ∘ (rrc _ _ f))  =  rrc _ _ (g ∘ f)

}.

Coercion rrc : RangeComb >-> rrcType.


(* rrc5 for all maps *)
Definition rrc5_all `{rrc : RangeComb} : Prop. 
  destruct rrc. 
  exact (forall (a b c : RC) (f : Hom a b) (g h : Hom b c), g ∘ f = h ∘ f -> g ∘ (rrc0 a b f) = h ∘ (rrc0 a b f)).
Defined.

(* rrc5 *)
Definition rrc5 `{rrc : RangeComb} (a b c : RC) (f : Hom a b) (g h : Hom b c) : Prop. 
  destruct rrc. 
  exact ( g ∘ f = h ∘ f <-> g ∘ (rrc0 a b f) = h ∘ (rrc0 a b f)).
Defined.

(* Range category *)
Class RangeCat `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) `(rrc : @RangeComb RC rc RC) : Type :=
{
  RCat_RRC : RangeComb := rrc
}.

(* define coercion *)
Instance RangeCatsAreRestCategories `(C : Category) `(rc : @RestrictionComb C) `(RC : @RestrictionCat C rc) 
  `(rrc : @RangeComb RC rc RC)  `{ RanC: @RangeCat C rc RC rrc } 
  : RestrictionCat C rc := RC.

Coercion RangeCatsAreRestCategories : RangeCat >-> RestrictionCat.

(* parial inverse *)
Definition partial_inverse `{CRC : CartRestrictionCat} (a b : RC) (f : Hom a b) (f_inv : Hom b a) : Prop :=
  (f ∘ f_inv = (rc _ _ f_inv)) /\ (f_inv ∘ f = (rc _ _ f)).

(* partial inverses in a cartesian restriction category are open *)
Lemma crc_open `{CRC : CartRestrictionCat} (a b : RC) (f : Hom a b) :
  (exists f_inv, partial_inverse a b f f_inv) -> (open a b f).
Proof. Admitted.

Definition exist_f `{RC : RestrictionCat} (rrc : RangeComb ) (a b : RC) (f : Hom a b) : Op a → Op b.
  intros. destruct rrc. destruct X. exists (rrc0 _ _ (f ∘ x)). rewrite rrc6. auto.
Defined.

(* whenever there exist maps exist_f for all maps f : a to b in given CRC, the range combinator at f in CRC
    must be equal to exist_f (Id b) *)
Definition is_range_comb `{RC : RestrictionCat}  (exist1_f : forall (a b : RC), (Op a) → (Op b)) 
   (is_exist_map : forall (a b : RC) (f : Hom a b), open_exist_f _ _ f (exist1_f a b)  )  : 
      forall (rrco : RangeComb ) (rr5_ex : @rrc5_all C RCat_RC RC rrco ) (a b : RC)  (f : Hom a b)  ,  
        rrc a b f = proj1_sig (exist1_f a b (exist _ (id a) (@IdIsTotal C RCat_RC RC a ))).
Admitted.

(* ranges and retractions *)
(* (4) defines a new embedding retraction pair 
    for x whenever rrc5 is satisfied in C, and gives a restriction idempotent on y *)
Lemma ranges_retractions `{RRC : RangeCat} : forall ( x y : RC), forall (m : Hom x y), 
  forall (r : Hom y x), (r ∘m = id x) -> 
(* 1 *) ( (rrc _ _ m = rrc _ _ (m ∘ r)) /\
(* 2 *)   (rrc _ _ r = (id x)) /\
(* 3 *)  (r ∘m = (r ∘(rrc _ _ m)) ∘m) /\ 
(* 4 *)  ((rrc5 _ _ _ (m ∘ r) (m ∘ r) (id) ) ->  (m ∘ r ∘ (rrc _ _ (m∘ r))) = rc _ _ ((m ∘ r) ∘ (rrc _ _ (m∘ r))))).
(* ( rc _ _ ((r ∘(rrc _ _ m)) ∘m ) = (r ∘(rrc _ _ m)) ∘m )  ) ). *)
Proof.
destruct RC. replace RCat_RC with rc0 in rc_d. Focus 2. auto.
  intros; split; try split ; try intros; try split;
  destruct C; destruct RRC; destruct rrc0; 
  destruct RCat_RRC0; destruct RCat_RC; simpl.

(* proof of (4)  *)
Focus 4. intro.
unfold rrc5 in H0. destruct H0. compute in H0.
assert (compose y y y (compose y x y r m) (compose y x y r m) =
     compose y y y (compose y x y r m) (id y)).
rewrite id_unit_left. rewrite  assoc.
rewrite <- (assoc _ _ _ _ r m).  compute in H. 
rewrite H. rewrite id_unit_left. auto.
generalize (H0 H2); intro. rewrite id_unit_left in H3.
destruct rc0. simpl.
compute in rc_d.  
rewrite H3. compute in rrc6. rewrite rrc6.
rewrite <- assoc. auto. 
(* 1 - 3 *)
Admitted.

(* corresponds to (ii) in the lemma in thesis - do not require a range combinator for this  *)
Lemma ranges_retr_open `{CRC : CartRestrictionCat} : forall ( x y : RC), forall (m : Hom x y), 
  forall (r : Hom y x), (r ∘m = id x) -> 
(open  y x r) /\ (open _ _ (m ∘ r)) 
/\ (forall (e : Op y) (exist_f_mr : (Op y) -> (Op y)) (exist_f_r : (Op y) -> (Op x)), 
    (open_exist_f _ _ r exist_f_r) -> (open_exist_f _ _ (m ∘ r) exist_f_mr) ->
      (proj1_sig (exist_f_r e) = proj1_sig (f_star _ _ m (exist_f_mr e))) ) .
Admitted.

(* corresponds to (ii) in the lemma in thesis - do not require a range combinator for this  *)
Lemma ranges_retr_open_rc `{CRC : CartRestrictionCat} : forall ( x y : RC), forall (m : Hom x y), 
  forall (r : Hom y x) (pfid : r ∘m = id x) (pfrc : rc _ _ (m ∘r) = (m ∘r)) , 
(open _ _ m ) /\
(forall (e : Op x) (exist_f_mr : (Op y) -> (Op y)) (exist_f_m : (Op x) -> (Op y)), 
   (open_exist_f _ _ m exist_f_m) -> (open_exist_f _ _ (m ∘ r) exist_f_mr) ->
    (proj1_sig (exist_f_m e) = proj1_sig (exist_f_mr (f_star _ _ r e)))   ).
Admitted.

Instance RangeCatIsRC `{ RRC: RangeCat  }  : RestrictionCat C RCat_RC  := RC.

Coercion RangeCatIsRC : RangeCat >-> RestrictionCat.

(* Beck-Chevalley condition for range categories *)
Definition Beck_Chevalley `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(rrco : @RangeComb CRC rco CRC) `(RRC : @RangeCat CRC rco CRC rrco)
 ( x y x' y' : RC) (f : Hom x y) ( g : Hom x' y' ) : Prop.
  destruct (RCat_HP y y') as [yXy']. destruct (RCat_HP x x') as [xXx']. 
  exact (rrc _ _ (pProd_morph_ex xXx' (f ∘ Pi_1p0) (g ∘ Pi_2p0)) = 
            pProd_morph_ex yXy' ((rrc _ _ f) ∘ Pi_1p ) ((rrc _ _ g) ∘ Pi_2p)).
Defined. 

(* given f, g, <f,g> satisfies BCC *)
Definition sat_Beck_Chevalley `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(rrco : @RangeComb CRC rco CRC) `(RRC : @RangeCat CRC rco CRC rrco)
   : Type := ∀ x y x' y' f g , 
    Beck_Chevalley C rco RC CRC rrco RRC  x y x' y' f g.

Definition Op_comp_pf `{CRC : CartRestrictionCat} 
 ( x x' : CRC) (opx : Op x) (opx' : Op x') : 
rc (RCat_HP x x') (RCat_HP x x') (pProd_morph_ex (RCat_HP x x') ((proj1_sig opx)∘ Pi_1p) ((proj1_sig opx')∘ Pi_2p)) =
pProd_morph_ex (RCat_HP x x') ((proj1_sig opx)∘ Pi_1p) ((proj1_sig opx')∘ Pi_2p) .
Admitted.

Definition Op_comp `{CRC : CartRestrictionCat} 
 ( x x' : CRC) (opx : Op x) (opx' : Op x') : Op (RCat_HP x x').
unfold Op.
exists (pProd_morph_ex (RCat_HP x x') ((proj1_sig opx)∘ Pi_1p) ((proj1_sig opx')∘ Pi_2p)).
apply Op_comp_pf.
Defined.

(* id is open *)
Definition id_open `{CRC : CartRestrictionCat} (a : CRC) : 
open_exist_f a a (id a) (fun b => b).
unfold open_exist_f. unfold Op_par_leq. unfold op_wedge.
destruct CRC. destruct RC. destruct C. 
simpl. unfold Op. destruct rc0. simpl. destruct RCat_RC. 
split; intros. destruct e' as [ea erc']. simpl.
Admitted.

(* a -> 1 x a map is open *)
Definition Ato1xAopen `{CRC : CartRestrictionCat} (a : CRC) : 
open a (RCat_HP RCat_term a) (pProd_morph_ex a (pt_morph a) (id a)).
unfold open_exist_f. unfold Op_par_leq. unfold op_wedge.
destruct CRC. destruct RC. destruct C. 
simpl. unfold Op. destruct rc0. simpl. destruct RCat_RC. 
Admitted.

(* Beck-Chevalley condition for range categories - open map version *)
Definition Beck_Chevalley_open `{CRC : CartRestrictionCat} 
 ( x y x' y' : CRC) (f : Hom x y) ( g : Hom x' y' ) 
   := open _ _ f -> open _ _ g -> 
    open (RCat_HP x x') (RCat_HP y y') (pProd_morph_ex (RCat_HP x x') (f ∘ Pi_1p) (g ∘ Pi_2p)) /\
  (forall (exist_f : Op x -> Op y) (exist_g : Op x' -> Op y')
  (ex_f_op : open_exist_f x y f exist_f) (ex_g_op : open_exist_f x' y' g exist_g)  
   (exist_fg : Op (RCat_HP x x') -> Op (RCat_HP y y')), forall (opfg : open_exist_f (RCat_HP x x') (RCat_HP y y') 
    (pProd_morph_ex (RCat_HP x x') (f ∘ Pi_1p)
      (g ∘ Pi_2p)) 
        exist_fg) (opx : Op x) (opx' : Op x'),
       ((pProd_morph_ex (RCat_HP y y') ((proj1_sig (exist_f opx)) ∘ Pi_1p)
      ((proj1_sig (exist_g opx')) ∘ Pi_2p)) = 
      (proj1_sig (exist_fg  (Op_comp x x' opx opx')  )  )) ).



(* a range category with a restriction terminal object, restriction products, 
   and satisfying the BCC is a Cartesian range category *)
Class CartRangeCat `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (rrco : @RangeComb CRC rco CRC) `(RRC : @RangeCat  CRC rco CRC rrco ) : Type :=
{
  RCat_BCC : sat_Beck_Chevalley C rco RC CRC rrco RRC 
}.

Instance CartRangeCatIsCRC `{ CRRC: CartRangeCat  }  : CartRestrictionCat  RCat_RC  := CRC.
Instance CartRangeCatIsRRC `{ CRRC: CartRangeCat  }  : RangeCat  RRC RCat_RC RRC RCat_RRC  := RRC.

Coercion CartRangeCatIsCRC : CartRangeCat >-> CartRestrictionCat.
Coercion CartRangeCatIsRRC : CartRangeCat >-> RangeCat.


(* weak range combinator *)
Definition weak_ranComb `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(rrco : @RangeComb CRC rco CRC) `(@RangeCat CRC rco CRC rrco)
  `(CRRC : @CartRangeCat  CRC rco CRC CRC rrco _ )  `(A : CRRC) `{ T : @TuringCat CRRC rco CRRC CRRC A } 
  (bullet : Hom (RCat_HP A A) A) (is_tur : TuringMorph _ _ _ _ A T bullet)  :=  forall (x y : T),
forall (f : Hom x y), exists (rf : @point CRRC rco CRRC CRRC A), forall (my : Hom y A), forall (ry : Hom A y), 
ry ∘ my = id y -> 
ry ∘ bullet ∘ (pProd_morph_ex y (compose _ _ _ _ (pt_morph y) (proj1_sig rf)) my) = rrc _ _ f.

(* strong range combinator *)
Definition strong_ranComb `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(rrco : @RangeComb CRC rco CRC) `(@RangeCat CRC rco CRC rrco)
  `(CRRC : @CartRangeCat  CRC rco CRC CRC rrco _ )  `(A : CRRC) `{ T : @TuringCat CRRC rco CRRC CRRC A } 
  (bullet : Hom (RCat_HP A A) A) (is_tur : TuringMorph _ _ _ _ A T bullet)  :=  exists (r : @point CRRC rco CRRC CRRC A),
forall (x y : T), forall (f : Hom x y), forall (my : Hom y A), forall (ry : Hom A y), 
ry ∘ my = id y -> 
ry ∘ bullet ∘ (pProd_morph_ex y (compose _ _ _ _ (pt_morph y) (proj1_sig r)) my) = rrc _ _ f.

(*
Definition make_point `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (A : CRC) (p : Hom RCat_term A) 
   (pt : TotMaps rco CRC RCat_term A p) : @point C rco RC CRC A.
exists p. unfold TotMaps in pt.  destruct rco. destruct RC. destruct CRC.
destruct C. simpl in pt.
simpl. auto.
Defined.

Print make_point. *)

(* identity map betweek Op a and Op a is open *)
Definition OpId `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) (b : CRC) : Op b.
 unfold Op. exists id. exact (IdIsTotal b).
Defined.


(* sufficient conditions to define range combinator in a Turing category *)
Definition bullet_points_open_range `(C : Category) `(rco : @RestrictionComb C) `(RC : @RestrictionCat C rco) 
  `(CRC : @CartRestrictionCat C rco RC) `(A : CRC) `{ T : @TuringCat CRC rco CRC CRC A } 
  (bullet : Hom (RCat_HP A A) A) 
  (index_col : forall (z:T) (f : Hom (RCat_HP z A) A), {h : Hom z A |
     TotMaps rco CRC z A h
     ∧ f =
       bullet ∘ pProd_morph_ex (RCat_HP z A) (h ∘ Pi_1p) Pi_2p})
  (emb_col : forall x : T, { mrx : prod (Hom x A) ( Hom A x ) | ((snd mrx) ∘ (fst mrx)) = id x } ) 
  (bcc_op : forall x y x' y' f g , @Beck_Chevalley_open C RCat_RC RC CRC x y x' y' f g ) : 
 (@open  CRC _ _ _ _ bullet)  ->  (forall (x y : CRC ) (m : Hom x y)  (r : Hom y x), (r ∘m = id x) -> rc _ _ (m ∘ r) = (m ∘ r) ) ->
  (forall (p :  @point CRC rco CRC CRC A), @open CRC _ _ _ _ (proj1_sig p)) ->
      forall a b f_map, (@open  CRC _ _ a b f_map).
unfold point. 
unfold open. (* unfold open_exist_f. unfold Op_par_leq. *)
intros. destruct H as [exist_fA].
destruct (emb_col a) as [[ma ra] mra]. simpl in mra.
destruct (emb_col b) as [[mb rb] mrb]. simpl in mrb.
destruct (index_col RCat_term  (mb ∘ f_map ∘ ra ∘ (Pi_2p) )) as [h [toth bul_h]].
unfold Op. unfold TotMaps in toth. destruct rco. simpl. destruct RC. simpl in toth.
destruct (H1 (exist (λ p0 : Hom RCat_term A, rc RCat_term A p0 = id) h toth)) as [opmaph openh].
generalize (bcc_op RCat_term A A A (h) (id A)). 
unfold Beck_Chevalley_open. intro bcc1A. 
assert (open RCat_term A h). unfold open.
exists opmaph. exact openh.
assert ( open A A id). unfold open. exists (fun a => a). exact (id_open A).
destruct (bcc1A H2 H3) as [openhid bcchid]. destruct openhid as [hidhat openhid].
simpl in H0.  
destruct (ranges_retr_open_rc a A ma ra mra (H0 _ _ ma ra mra)) as [op_ra mra_pf].
destruct (ranges_retr_open b A mb rb mrb) as [op_rb mrb_pf].
destruct op_rb as [op_rb op_rb_pf]. destruct op_ra as [mra_op mra_eq]. 
 destruct (Ato1xAopen A) as [ato1amap ato1apf].
eexists. Unshelve. Focus 2. intro opa.
exact (op_rb ( exist_fA (hidhat ( ato1amap (mra_op opa)) ) ) ).
replace f_map with (rb ∘ (bullet  ∘ ((pProd_morph_ex (RCat_HP RCat_term A) (h ∘ Pi_1p) (id ∘ Pi_2p))
  ∘ ((pProd_morph_ex A (pt_morph A) (id A)) ∘ ma)))).
Print composition_open_mapex. 
apply (composition_open_mapex a A b 
       (bullet  ∘ ((pProd_morph_ex (RCat_HP RCat_term A) (h ∘ Pi_1p) (id ∘ Pi_2p))
  ∘ ((pProd_morph_ex A (pt_morph A) (id A)) ∘ ma))) rb
  (fun opa => (exist_fA (hidhat (ato1amap (mra_op opa))))) op_rb) ; try auto.  
apply (composition_open_mapex a (RCat_HP A A) A 
       ( ((pProd_morph_ex (RCat_HP RCat_term A) (h ∘ Pi_1p) (id ∘ Pi_2p))
  ∘ ((pProd_morph_ex A (pt_morph A) (id A)) ∘ ma))) bullet
  (fun opa => ( (hidhat (ato1amap (mra_op opa))))) exist_fA) ; try auto.  
apply (composition_open_mapex a (RCat_HP RCat_term A) (RCat_HP A A)
       ( ( ((pProd_morph_ex A (pt_morph A) (id A)) ∘ ma))) (pProd_morph_ex (RCat_HP RCat_term A) (h ∘ Pi_1p) (id ∘ Pi_2p))
  (fun opa => ( ( (ato1amap (mra_op opa))))) hidhat) ; try auto. 
apply (composition_open_mapex a A (RCat_HP RCat_term A)
       ma (pProd_morph_ex A (pt_morph A) (id A)) 
  (fun opa => ( ( ( (mra_op opa))))) ato1amap) ; try auto. 
destruct (xX1and1XxIsox CRC A RCat_term ) as [Ax1is tXAiso].
rewrite (ProdMapComp CRC). rewrite id_unit_left.
 rewrite <- assoc. rewrite <- assoc. 
rewrite <- assoc. rewrite <- (ProdMapComp CRC). apply symmetry.

Check @pProd_morph_ex.
   replace ( f_map ) with (
 (rb ∘ (mb ∘ f_map ∘ ra ∘ 
  Pi_2p) ∘ (@pProd_morph_ex CRC _ CRC (@p_term C _ CRC RCat_term ) A 
   (RCat_HP (@p_term C _ CRC RCat_term ) A )
   A (@pt_morph C _ CRC RCat_term A) (id A)) ∘ ma ) ).
rewrite bul_h. rewrite assoc. rewrite assoc.
rewrite (ProdMapComp CRC). rewrite <- assoc. rewrite <- assoc.
rewrite <- assoc. rewrite <- (ProdMapComp CRC). rewrite assoc. auto.
rewrite <- assoc. rewrite <- assoc. rewrite <-assoc. rewrite mrb.
rewrite id_unit_left.
replace (((f_map ∘ ra ∘ Pi_2p) ∘ (@pProd_morph_ex CRC _ CRC (@p_term C _ CRC RCat_term ) A 
   (RCat_HP (@p_term C _ CRC RCat_term ) A ) A (pt_morph A) id)) ∘ ma) with
(((f_map ∘ ra) ∘ (Pi_2p ∘ (@pProd_morph_ex CRC _ CRC (@p_term C _ CRC RCat_term ) A 
   (RCat_HP (@p_term C _ CRC RCat_term ) A ) A (pt_morph A) id))) ∘ ma).
destruct C. simpl. simpl in tXAiso.
destruct (tXAiso (RCat_HP RCat_term A )). rewrite <- H5.
rewrite id_unit_right. rewrite assoc. simpl in mra. rewrite mra.
rewrite id_unit_right. auto.
rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. auto.
Defined. 






(* Trial Code *)

(* existence of exist_fg *)
Definition Beck_Chevalley_open_exists `{CRC : CartRestrictionCat} 
 ( x y x' y' : CRC) (f : Hom x y) ( g : Hom x' y' )  := 
forall (exist_f : Op x -> Op y) (exist_g : Op x' -> Op y') 
  (ex_f_op : open_exist_f x y f exist_f) (ex_g_op : open_exist_f x' y' g exist_g), 
  exists (exist_fg : Op (RCat_HP x x') -> Op (RCat_HP y y')), forall (opfg : open_exist_f (RCat_HP x x') (RCat_HP y y') 
    (pProd_morph_ex (RCat_HP x x') (f ∘ Pi_1p)
      (g ∘ Pi_2p)) 
        exist_fg) (opx : Op x) (opx' : Op x'), 
       ((pProd_morph_ex (RCat_HP y y') ((proj1_sig (exist_f opx)) ∘ Pi_1p)
      ((proj1_sig (exist_g opx')) ∘ Pi_2p)) = 
      (proj1_sig (exist_fg  (Op_comp x x' opx opx')  )  )).


(* bcc implies range of product exists *)
Definition bcc_open_imp_exists `{CRC : CartRestrictionCat} 
 ( x y x' y' : CRC) (f : Hom x y) ( g : Hom x' y' ) 
 : Beck_Chevalley_open x y x' y' f g  ->
  Beck_Chevalley_open_exists x y x' y' f g .
unfold Beck_Chevalley_open. unfold Beck_Chevalley_open_exists.
simpl. intros. destruct CRC. simpl. 
eexists. Unshelve. Focus 2. unfold Op. 
intro. (*
generalize (H exist_f0 exist_g ex_f_op ex_g_op). simpl.
intro exfg.
clear H. *) destruct X as [exx' rcxx'].
eexists. Unshelve. Focus 2.
destruct (RCat_HP x x') as [xXx']. simpl in exx'. simpl in rcxx'.
(*
exact (pProd_morph_ex (RCat_HP y y')
         (proj1_sig (exist_f0 opx) ∘ Pi_1p)
         (proj1_sig (exist_g opx') ∘ Pi_2p)).
generalize ((Op_comp_pf _ _ (exist_f0 opx) (exist_g opx'))).
 simpl. intro. auto.
simpl. intro. auto.
Defined. *)
Admitted.