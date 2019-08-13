Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.


Check Nat.lt.
Check lt.
Goal Nat.lt = lt. Proof. auto. Qed.

Notation "a >=? b" := (Nat.leb b a)
                          (at level 70, only parsing) : nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                       (at level 70, only parsing) : nat_scope.
Notation " a =? b" := (beq_nat a b)
                        (at level 70) : nat_scope.

Print reflect.

Print iff_reflect.

Print beq_nat_true_iff.
(* BX-52K2LT7NG5GQ *)

(* x is true if and only if y is true *)
Lemma beq_reflect: forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.
  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Example reflect_example1: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros a.
  destruct (blt_reflect a 5) as [H|H].
  omega.
  omega.
Qed.

Hint Resolve blt_reflect beq_reflect: bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
    evar (e: Prop);
    assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
      [ | try first [apply not_lt in H | apply not_le in H]]].

Example reflect_example2 : forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a<?5).
  omega. omega.
Qed.

Ltac inv H := inversion H; clear H; subst.

Module Exploration1.

  Theorem omega_example1 :
    forall i j k,
      i < j ->
      not(k - 3 <= j) ->
      k > i.
  Proof.
    intros.
    omega. Qed.

  Theorem bogus_substraction: not(forall k:nat, k > k -3).
  Proof.
    intro.
    specialize (H O).
    simpl in H.
    inversion H.
  Qed.

  Theorem omega_example2:
    forall i j k,
      i < j ->
      not (k - 3 <= j) ->
      k > i.
  Proof.
    intros.
    apply not_le in H0.
    unfold gt in H0.
    unfold gt.
    (* unify everything to <  aviod  > of bogus...*)
    Search (_ < _ -> _ <= _ -> _ < _).
    apply Nat.lt_le_trans with j.
    apply H.
    apply le_trans with (k-3).
    Search (_ < _ -> _ <= _).
    apply lt_le_weak.
    auto.
    apply le_minus.
  Qed.

  (* wap the first two elements of a list, if they are out of order .*)
  Definition maybe_swap (al: list nat): list nat :=
    match al with
    | a :: b :: ar => if a >? b then b::a::ar else a::b::ar
    | _ => al
    end.

  Example maybe_swap_123:
    maybe_swap [1;2;3] = [1;2;3].
  Proof.
    reflexivity. Qed.

  Example maybe_swap_321:
    maybe_swap [3; 2; 1] = [2; 3; 1].
  Proof. reflexivity. Qed.
  
  Theorem maybe_swap_idempotent:
    forall al, maybe_swap (maybe_swap al) = maybe_swap al.
  Proof.
    intros.
    (* we only care about first two number, destruct them*)
    destruct al as [ | a al].
    simpl.
    reflexivity.
    destruct al as [ | b al].
    reflexivity.
    simpl.
    (* there is only <? in coq so we should use some blt
     in order to use omega, we need prop rather than bool
     so use blt reflect instead *)
    destruct (blt_reflect b a).
    * simpl. destruct (blt_reflect a b).
      omega. reflexivity.
    * simpl. bdestruct(b<?a).
      omega. reflexivity.
  Qed.

  Locate Permutation.
  Check  Permutation.

  (* if the elements of al can be reordered (without insertions or deletions) to get the list bl.
*)
  Check perm_skip.
  Check Permutation_refl.
  Check Permutation_app_comm.
  Check app_assoc.

  Print Permutation_app_comm.
  Lemma extract_h: forall (a:nat) (l: list nat),
      (a::l) = [a] ++ l.
  Proof.
    intros.
    simpl. reflexivity. Qed.

  Example permut_example: forall (a b: list nat),
      Permutation (5::6::a++b) ((5::b)++(6::a++[])).
  Proof.
    intros.
    simpl.
    rewrite app_nil_r.
    apply perm_skip.
    rewrite app_comm_cons.
    apply Permutation_app_comm.
  Qed.

    


  End Exploration1.
