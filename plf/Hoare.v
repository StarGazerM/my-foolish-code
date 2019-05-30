Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Imp.

Definition Assertion := state -> Prop.

Module ExAssertations.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            not (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertations.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P: Assertion) (c: com) (Q: Assertion): Prop :=
  forall st st',
    st =[ c ]=> st' ->
               P st ->
               Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, not (P st)) ->
  {{ P }} c {{ Q }}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.
Qed.

Definition assn_sub X a P: Assertion :=
  fun (st: state) =>
    P (X !-> aeval st a; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).


Theorem hoare_asgn : forall Q X a,
    {{Q [ X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H;subst.
  unfold assn_sub in H0.
  assumption.
Qed.

Example assn_sub_example:
  {{(fun st => st X < 5)[X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn. Qed.

