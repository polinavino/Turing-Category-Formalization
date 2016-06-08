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


Open Scope nat_scope.

Open Scope list_scope.

Inductive prf : Type := 
| Zero : prf
| Succ : prf 
| Proj : nat -> prf
| Sub : prf -> prf -> nat -> nat -> prf
| Rec : prf -> prf -> prf
| Min : prf -> prf.

Definition prf_n : Type := list prf. 

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


Definition zel : nat -> list nat -> nat.
Proof.
  intros.
  exact ( match (blt_nat (length H0) H) with
       | true => H
       | false => 0
     end ).
Defined.

Fixpoint pcombine (n m : nat) (l : list nat) (x : nat) : list nat.
Proof. 
  exact (match m with 
           | 0 => cons (zel n l) (cons x nil)
           | S m' => cons (zel n l) (pcombine (S n) m' l x) end).
Defined.

(* The following two definitions give the semantics for minimalization *)
Inductive allsucs : (nat -> nat -> Prop) -> nat -> Prop :=
  | allsucs_zero : forall (k : nat), forall (R : nat -> nat -> Prop), (R 0 (S k)) -> allsucs R 0
  | allsucs_Sn : forall (m k : nat), forall (R : nat -> nat -> Prop), R (S m) (S k) -> allsucs R m -> allsucs R (S m).

Inductive minl : (nat -> nat -> Prop) -> nat -> Prop :=
  | minl_zero : forall (R : nat -> nat -> Prop), (R 0 0) -> minl R 0
  | minl_Sn : forall (n : nat), forall (R : nat -> nat -> Prop), R (S n) 0 -> allsucs R n -> minl R (S n).


Inductive converges_to_tot : prf -> list nat -> nat -> Prop :=
  | conv_zero : forall (l : list nat), converges_to_tot Zero l 0
  | conv_succ : converges_to_tot Succ nil (S 0) 
  | conv_succ_nil : forall (l : list nat), forall x : nat, converges_to_tot Succ (cons x l) (S x) 
  | conv_proj : forall (l : list nat), forall i : nat, converges_to_tot (Proj i) l (zel i l) 
  | conv_sub : forall (l : list nat), forall (f g : prf), forall (n m x y : nat), converges_to_tot g l x 
    -> converges_to_tot f (pcombine n m l x) y ->
       converges_to_tot (Sub f g n m) l y
  | conv_pr_nil : forall (B s : prf), forall (x : nat), converges_to_tot B nil x -> converges_to_tot (Rec B s) nil x
  | conv_pr_l : forall (l : list nat), forall (B s : prf), forall (x : nat), converges_to_tot B l x 
    -> converges_to_tot (Rec B s) (cons 0 l) x
  | conv_pr : forall (l : list nat), forall (B s : prf), forall (x h r: nat), converges_to_tot (Rec B s) (cons h l) r ->
       converges_to_tot s (cons h (cons r l)) x -> converges_to_tot (Rec B s) (cons (S h) l) x .



(* prf convergence including minimalization *)
Inductive converges_to : prf -> list nat -> nat -> Prop :=
  | conv_to_tot : forall f : prf, forall ln : list nat, forall x : nat, 
    converges_to_tot f ln x -> converges_to f  ln x
  | conv_min : forall f : prf, forall ln : list nat, forall x : nat,  (minl (fun (h : nat) => (converges_to_tot f (cons h ln) )) x) ->
      converges_to (Min f)  ln  x.

(*
Inductive converges_to : prf -> (forall (P : list nat -> Prop),  forall ln : list nat, P ln -> nat -> Prop) :=
  | conv_to_tot : forall f : prf, forall ln : list nat, forall x : nat, 
    converges_to_tot f ln x -> converges_to f (fun (h : list nat) => True) ln I x
  | conv_min : forall f : prf, forall ln : list nat, forall x : nat,  forall dom_f : (minl (fun (h : nat) => (converges_to_tot f (cons h ln) )) x) ,
      (minl (fun (h : nat) => (converges_to_tot f (cons h ln) )) x) ->
      converges_to f (fun (hn : list nat) => (minl (fun (h : nat) => (converges_to_tot f (cons h hn) )) x) ) ln dom_f x.
*)

(* convergence for a list of functions *)
Fixpoint conv_prf_list (P : list nat -> Prop) (lf : list prf) (x : list nat) (w : P x) (y : list nat) : Prop :=
(match lf with 
           | nil => (match y with 
                            | nil => True
                            | h :: y' => False end)

           | f :: lf' => (match y with 
                            | nil => False
                            | h :: y' => (converges_to f P x w h) /\ (conv_prf_list P lf' x w y') end) end).

(* define obj and hom in the Comp(N) category *)
Definition CompN_Obj : Type := { n : nat & { ln : list nat | length ln = n} }.

Definition CompN_Morph (A B : CompN_Obj) : Type.
Proof.
  destruct A. destruct B. destruct s. destruct s0.
  exact  ({ P : list nat -> Prop & {lf : list prf | (length lf = x0) /\
    forall w : P x1, conv_prf_list P lf x1 w x2}}).
Defined.

(*
Definition CompN_cProp (A B C : CompN_Obj) : CompN_Morph A B -> CompN_Morph B C -> (list nat -> Prop).
Proof.
  intros h1 h2 ln. destruct A; destruct B; destruct C. 
  destruct s; destruct s0; destruct s1. destruct h1; destruct h2.
  destruct s as [lst_prf1]; destruct s0 as [lst_prf2]. 
  induction lst_prf2 as [f2 | lst2];
  destruct a; destruct a0.
  exact True. 
  induction x4 as [c | cl].
  rewrite <- e1 in H1. inversion H1.



exact IHlst_prf2.
  induction x1. inversion H1.
  inversion H1.
  

 clear.
  rewrite (proj1 (length_zero_iff_nil x4) H1). auto.
  induction lst_prf1 as [f1 | lst1] ; 
*)

(* compose a prf : N^n -> N with a list of n prf's - not finished *)
Definition CompN_comp1 (A B : CompN_Obj) : CompN_Morph A B -> prf -> list prf.
Proof.
  intros h1 p. destruct A; destruct B. 
  destruct s; destruct s0. destruct h1.
  induction s as [lst_prf1]. destruct p0.
  
; induction s0 as [lst_prf2]. 
  destruct p; destruct p0.
  compute. 

(* compose lists of prf's - not finished *)
Definition CompN_composition (A B C : CompN_Obj) : CompN_Morph A B -> CompN_Morph B C -> CompN_Morph A C.
Proof.
  intros h1 h2. destruct A; destruct B; destruct C. 
  destruct s; destruct s0; destruct s1. destruct h1; destruct h2.
  induction s as [lst_prf1]; induction s0 as [lst_prf2]. 
  destruct p; destruct p0.
  compute. 
  exists (fun (ln : list nat) => ((x5 ln) /\ (∀ w : x5 ln, conv_prf_list x5 lst_prf1 ln w x3) /\ (x6 x3))).
  compute. 
  induction (length lst_prf2) as [l | sl].
  
 ; induction lst_prf2 as [f2 | lst2].
  exists (fun (l : list nat) => True).
  exists nil. split. compute in H1. auto. 
  intro. compute in H1. rewrite <- e1 in H1. apply symmetry in H1.
  rewrite (proj1 (length_zero_iff_nil x4) H1). auto.

  compute in H2. destruct x1. 
  generalize (proj1 (length_zero_iff_nil (lst2 :: lst_prf2)) H1).
  intro. inversion H3.
  compute in H2; compute in IHlst_prf2. 
  inversion H1. rewrite H4. 
  apply projT1 .
  split.
 compute.

 rewrite  in H1.
  assert (x4 = nil). induction x4. auto. compute. apply H1.
  rewrite <- H1. compute. destruct x4. auto.  inversion w. 
length (lst2 :: lst_prf2) = x1
 apply induction. esplit. intro. exists. inversion. unfold converges_to.

 apply proj1_sig . inversion lst_prf . split. apply exists.
  destruct s; destruct s0. compute.
  destruct snd. destruct snd0. destruct snd1. compute. 
  compute in c.


(* The rest of  code is formalizing some more things described in V. Zammit's paper
We will likely take a slightly different approach to the rest of the formalization of Comp(N) *)

Axiom conv_min_ax : forall (l : list nat), forall (f : prf), forall (x : nat), (minl (fun (h : nat) => (converges_to f (cons h l) )) x) ->
       converges_to (Min f) l x.


Axiom conv_min_ax : forall (l : list nat), forall (f : prf), forall (x : nat), forall ml : (minl (fun (h : nat) => (converges_to f (cons h l) )) x), 
       converges_to (Min f) (fun (hn : list nat) => exists h1 : nat, (minl (fun (h : nat) => (converges_to f (cons h hn) )) h1 x) )  
        l (hd_pf) x.


Inductive converges_to : prf -> (forall (P : list nat -> Prop),  forall ln : list nat, P ln -> nat -> Prop) :=
  | conv_zero : forall (l : list nat), converges_to Zero (fun (h : list nat) => True) l I 0
  | conv_succ : converges_to Succ (fun (h : list nat) => True) nil I (S 0) 
  | conv_succ_nil : forall (l : list nat), forall x : nat, converges_to Succ (fun (h : list nat) => True) (cons x l) I (S x) 
  | conv_proj : forall (l : list nat), forall i : nat, converges_to (Proj i) (fun (h : list nat) => True) l I (zel i l) 
  | conv_sub : forall (l : list nat), forall (f g : prf), forall (n m x y : nat), converges_to g (fun (h : list nat) => True) l I x 
    -> converges_to f (fun (h : list nat) => True) (pcombine n m l x) I y ->
       converges_to (Sub f g n m) (fun (h : list nat) => True) l I y
  | conv_pr_nil : forall (B s : prf), forall (x : nat), converges_to B (fun (h : list nat) => True) nil I x -> converges_to (Rec B s) (fun (h : list nat) => True) nil I x
  | conv_pr_l : forall (l : list nat), forall (B s : prf), forall (x : nat), converges_to B (fun (h : list nat) => True) l I x 
    -> converges_to (Rec B s) (fun (h : list nat) => True) (cons 0 l) I x
  | conv_pr : forall (l : list nat), forall (B s : prf), forall (x h r: nat), converges_to (Rec B s) (fun (h : list nat) => True) (cons h l) I r ->
       converges_to s (fun (h : list nat) => True) (cons h (cons r l)) I x -> converges_to (Rec B s) (fun (h : list nat) => True) (cons (S h) l) I x .



(*
Inductive minl : (nat -> nat -> Prop) -> nat -> Prop :=
  | minl_zero : forall (R : nat -> nat -> Prop), (R 0 0) -> minl R 0
  | minl_Sn_z : forall (n : nat), forall (R : nat -> nat -> Prop), R (S n) 0 -> allsucs R n -> minl R (S n).
  | minl_SmSk : forall (k n : nat), forall (R : nat -> nat -> Prop), R (S (S n)) 0 -> R (S n) (S k) -> allsucs R n  -> minl R (S n).


Inductive minl : (nat -> nat -> Prop) -> nat -> Prop :=
  | minl_zero : forall (R : nat -> nat -> Prop), (R 0 0) -> minl R 0
  | minl_Sn : forall (n : nat), forall (R : nat -> nat -> Prop), R (S n) 0 -> allsucs R n -> minl R (S n).
*)

Check (fun (h : list nat) => True).


Axiom conv_min_ax : forall (l : list nat), forall (f : prf), forall (x : nat), (minl (fun (h : nat) => (converges_to f (cons h l) )) x) ->
       converges_to (Min f) l x.


Definition consh_domain : forall P : list nat -> Prop, forall x : nat, (forall ln : list nat, P ln) -> prf -> 
    (exists ).
  intros P D f.

Fixpoint natarity (p : prf) : nat :=
match p with 
  | Zero => 0
  | Succ => (S 0)
  | Proj i => (S i)
  | Sub f g n m => max (natarity g) (n + m)
  | Rec b s => max (S (natarity b)) (pred (natarity s))
  | Min f => pred (natarity f )
end.

Theorem natr_thm : forall (p : prf), forall (l : list nat), forall (l0 : list nat), ((length l) = (natarity p)  ->
(forall x : nat,  ((converges_to p l x) <-> (converges_to p ( l ++ l0) x)))).
Proof. Admitted.  (*
  intros.
  split. compute. rewrite H. elim (converges_to p l x). converges_to.

  | conv_min : forall (l : list nat), forall (f : prf), forall (x : nat), (minl (fun (h : nat) => (converges_to f (cons h l) )) x) ->
       converges_to (Min f) l x.
*)

Fixpoint Subl_in (f : prf) (g : list prf) (m n : nat) : prf :=
match g with
  | nil => Sub f Zero 0 0
  | g1 :: gl => match gl with 
        | nil => Sub f g1 m n
        | g2 :: gl' => Sub (Subl_in f gl m (S n)) g1 0 (m + n)
      end
end.


Fixpoint maxarity (g : list prf) := 
match g with
  | nil => 0
  | g :: gl => max (natarity g) (maxarity gl)
end.

Definition Subl (f : prf) (gl : list prf) := (Subl_in f gl (maxarity gl) 0).

Fixpoint mapR (A : Type) (B : Type) (R : A -> B -> Prop) (lA : list A) (lB : list B) : Prop :=
match lA with
  | nil => match lB with 
        | nil => True
        | b :: lB' => False
       end
  | a :: lA' => match lB with 
        | nil => False
        | b :: lB' => (R a b) /\ (mapR A B R lA' lB')
       end
end.


Theorem Subl_thm : forall (f : prf), forall ( gl : list prf), forall (l : list nat), forall ( x : nat) ,
(converges_to (Subl f gl) l x) <->
(exists (xl : list nat), (mapR prf nat (fun (g : prf) => converges_to g xl) gl xl) /\
(converges_to f xl x)).
Proof.
  Admitted.

Inductive vect : Type -> nat -> Type := 
  | Vnil: forall (A : Type), (vect A 0)
  | Vcons : forall ( A : Type), forall (n : nat), nat -> (vect A n) -> (vect A (S n)).

Definition Change_arity (n m : nat) ( t : n = m) (A : Type) (v : vect A n) :  (vect A m).
Proof.
  rewrite <-t. auto. (* inversion v. rewrite t in H0. rewrite <- H0. exact (Vnil A). rewrite <- t. exact (Vcons A n H X). *)
Defined. 

Theorem Change_arity_eq :
forall (n : nat) , forall (t: (n=n)) , forall (A : Type) , forall (v : vect A n), (Change_arity n n t A v) = v.
Proof.
  intros. compute. induction v. 
replace (match t in (_ = y) return (vect A y) with
| eq_refl => Vnil A
end ) with (match (reflexivity 0) in (_ = y) return (vect A y) with
| eq_refl => Vnil A
end). compute. auto. rewrite (proof_irrelevance (0=0) (reflexivity 0) t). auto.
replace (match t in (_ = y) return (vect A y) with
| eq_refl => Vcons A n n0 v
end) with (match (reflexivity (S n)) in (_ = y) return (vect A y) with
| eq_refl => Vcons A n n0 v
end).

 compute. auto. rewrite (proof_irrelevance (S n = S n) (reflexivity (S n)) t). auto.
Defined.

Definition vhd: forall (A: Type) , forall (n: nat) , (vect A (S n)) -> A.
Proof.
  intros.
  induction n. Focus 2. exact IHX.

  destruct X. 
  exact (match X with 
          | Vnil A => 0
          | Vcons A (S n) a v => a  end).
  exact (math 
 exact (Vnil A).
 vtl: (A: Set) ! (n: nat) ! (vector A (S n)) ! (vector A n) and
 vel: (A: Set) ! (i, n: nat) ! (Hl: i < n) ! (vector A n) ! A

Fixpoint Vhd A (S n) (h; ~t) h
Vtl A (S n) n (h; ~t) ~t
Vel A 0 (S n) (h; ~t) h
Vel A i n ~t x
Vel A (S i) (S n) (h; ~t) x

(*
  | g1 :: g2 :: gl => Sub (Subl_in f (g2 :: gl) m ( n-1)) g1 0 n
end.

  | g1 :: g2 :: gl => Sub (Subl_in f (g2 :: gl) m (S n)) g1 0 (m + n)
end.

f m [g] n = Sub f g m n
f m g1 : g2 : gl n = 
end.
*)



Definition CompN_Obj := list nat.
  
Definition CompN_Morph : fun (a b : CompN_Obj) => { P : a -> Prop & {f : prf | forall x : a, forall w : P w, exists y, converges_to_in_domain f P a w y}}.