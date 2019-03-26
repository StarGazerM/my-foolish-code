Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le: nat -> nat -> Prop.

Check le: relation nat.

Definition partial_function {X: Type}(R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1=y2.


Inductive next_nat: nat -> nat -> Prop :=
  | nn: forall n:nat, next_nat n (S n).

Check next_nat: relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  inversion H. inversion H0.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  not(partial_function le).
Proof.
  unfold partial_function.
  unfold not.
  intros.
  discriminate (H 0 1 0).
  - apply le_S. apply le_n.
  - apply le_n.
Qed.


Definition reflexive {X: Type} (R: relation X) :=
  forall a: X, R a a.

Theorem le_reflexive:
  reflexive le.
Proof.
  unfold reflexive.
  intros. apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c: X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction  Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo.
Qed.


Theorem lt_trans :
  transitive lt.
Proof.
  unfold transitive.
  unfold lt.
  intros a b c Hab Hbc.
  induction Hbc.
  - apply le_S in Hab. apply Hab.
  - apply le_S in IHHbc. apply IHHbc.
Qed.

Theorem le_Sn_le: forall n m,
    (S n <= m) -> (n <= m).
Proof.
  intros n m H.
  apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.


Print le_trans.

Theorem le_S_n : forall n m,
    (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply le_Sn_le. apply H1.
Qed.

  
Definition symmetric {X: Type}(R: relation X) :=
  forall a b: X, (R a b) -> (R b a).



