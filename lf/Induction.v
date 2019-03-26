From LF Require Export Basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem multi_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite plus_n_O.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem plus_n_sm : forall n m:nat,
    S(n + m) = n + (S m).
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.

  
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_sm.
    reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
    (n + m) = (m + n).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_sm.
    reflexivity.
Qed.






