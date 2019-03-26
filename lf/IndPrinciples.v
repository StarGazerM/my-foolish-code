Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.


Check nat_ind.

Theorem mult_0_r' : forall n:nat,
    n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. apply H. Qed.


