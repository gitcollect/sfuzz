
(* Require Import QArith. *)

Require Import Arith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Inductive simList {X:Type} : list X -> list X -> Prop :=
  | simL_eq l1 l2 : eq l1 l2 -> simList l1 l2
  | simL_consS h1 t1 h2 t2 : eq h1 h2 -> simList t1 t2 -> simList (h1::t1) (h2::t2)
  | simL_cons1 h1 t1 h2 t2 : eq_nat (length t1) (length t2 + 1)
                         -> simList t1 (h2::t2)
                         -> simList (h1::t1) (h2::t2)
  | simL_cons2 h1 t1 h2 t2 : eq_nat (length t1 + 1) (length t2)
                         -> simList (h1::t1) t2
                         -> simList (h1::t1) (h2::t2)
.

Example simEx1 : simList [1;2] [2].
Proof. apply simL_cons1. reflexivity. apply simL_eq. reflexivity. Qed.

Example simEx2 : simList [1;2;3;4] [1;3;4].
Proof. apply simL_consS. reflexivity.
  apply simL_cons1. reflexivity. apply simL_eq. reflexivity. Qed.


Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P []
  | all_cons x l : P x -> all P l -> all P (x :: l).

Inductive simNat : nat -> nat -> Prop :=
  | simN_eq n1 n2 : eq_nat n1 n2 -> simNat n1 n2
  | simN_l n1 n2 : eq_nat (S n1) n2 -> simNat n1 n2
  | simN_r n1 n2 : eq_nat n1 (S n2) -> simNat n1 n2
.

Fixpoint sumList (l : list nat) : nat :=
  match l with
    | [] => 0
    | n :: l' => n + sumList l'
  end.

Example sumListEx1 : eq_nat 10 (sumList [1;2;3;4]).
Proof. reflexivity. Qed.


Lemma foo : forall (Arg Arg' : list nat),
  simList Arg Arg' ->
  all (fun x => x <= 1) Arg ->
  all (fun x => x <= 1) Arg' ->
  simNat (sumList Arg) (sumList Arg').
Proof. intros. inversion H.
  rewrite H2. apply simN_eq. apply eq_nat_refl.
  rewrite H2. simpl.






