
(* Require Import QArith. *)

Require Import Arith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Inductive simList {X:Type} : nat -> list X -> list X -> Prop :=
  | simL_eq l1 l2 : forall n, eq l1 l2 -> simList n l1 l2
  | simL_cons h t1 t2 : forall n, simList n t1 t2 -> simList n (cons h t1) (cons h t2)
  | simL_cons1 h1 l1 l2 : forall n, simList n l1 l2
                         -> simList (S n) (cons h1 l1) l2
  | simL_cons2 l1 h2 l2 : forall n, simList n l1 l2
                         -> simList (S n) l1 (cons h2 l2)
  | simL_weak l1 l2 : forall d, simList d l1 l2 -> simList (S d) l1 l2.

Example simEx1 : simList 1 [1;2] [2].
Proof. apply simL_cons1. apply simL_eq. reflexivity. Qed.

Example simEx2 : simList 1 [1;2;3;4] [1;3;4].
Proof. apply simL_cons. 
  apply simL_cons1. apply simL_eq. reflexivity. Qed.

Example simEx3 : simList 1 [] [1].
Proof. apply simL_cons2. apply simL_eq. reflexivity. Qed.

Lemma listConsEq : forall (X:Type) (a:X) l1 l2,
  l1 = l2 -> a::l1 = a::l2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma listConsEq' : forall (X:Type) (a:X) l1 l2,
  a::l1 = a::l2 -> l1 = l2.
Proof. intros. inversion H. reflexivity. Qed.

Lemma simLZeroEq : forall (X:Type) (l1 l2:list X),
  simList 0 l1 l2 -> l1 = l2.
Proof. intros X l1. induction l1. intros.
  inversion H. apply H0.
  intros. induction l2. inversion H. inversion H0.
  inversion H. apply H0.
  apply listConsEq. apply IHl1. apply H2.
Qed.

(*
Lemma simLOneOff : forall (X:Type) (x1 x2:X) (l1 l2:list X),
  simL 1 (x1::l1) (x2::l2) -> x1<>x2 -> l1 = l2.
*)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P []
  | all_cons x l : P x -> all P l -> all P (x :: l).

Inductive simNat : nat -> nat -> nat -> Prop :=
  | simN_eq n1 n2 : forall d, eq_nat n1 n2 -> simNat d n1 n2
  | simN_S n1 n2 : forall d, simNat d n1 n2 -> simNat d (S n1) (S n2)
  | simN_l n1 n2 : forall d, simNat d n1 n2 -> simNat (S d) (S n1) n2
  | simN_r n1 n2 : forall d, simNat d n1 n2 -> simNat (S d) n1 (S n2)
  | simN_weak n1 n2 : forall d, simNat d n1 n2 -> simNat (S d) n1 n2.

Lemma simNatPlus : forall (d n s1 s2 : nat),
  simNat d s1 s2 -> simNat d (n+s1) (n+s2).
Proof. intros. induction n.
  simpl. apply H.
  simpl. apply simN_S. apply IHn.
Qed.

Fixpoint sumList (l : list nat) : nat :=
  match l with
    | [] => 0
    | n :: l' => n + sumList l'
  end.

Example sumListEx1 : eq_nat 10 (sumList [1;2;3;4]).
Proof. reflexivity. Qed.



Lemma foo : forall (Arg Arg' : list nat) (d:nat),
  simList d Arg Arg' ->
  all (fun x => x <= 1) Arg ->
  all (fun x => x <= 1) Arg' ->
  simNat d (sumList Arg) (sumList Arg').
Proof. intros. induction H.
  rewrite H. apply simN_eq. apply eq_nat_refl.
  simpl. apply simNatPlus. apply IHsimList.
    inversion H0. apply H5. inversion H1. apply H5.
  inversion H0. inversion H4. simpl. apply simN_l. apply IHsimList.
    apply H5. apply H1.
    inversion H7. simpl. apply simN_weak. apply IHsimList.
      apply H5. apply H1.
  inversion H1. inversion H4. simpl. apply simN_r. apply IHsimList.
    apply H0. apply H5.
    inversion H7. simpl. apply simN_weak. apply IHsimList.
      apply H0. apply H5.
  apply simN_weak. apply IHsimList. apply H0. apply H1.
Qed.






