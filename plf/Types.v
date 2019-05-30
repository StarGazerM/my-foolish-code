Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.
Hint Constructors multi.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.
Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).
Definition value (t : tm) := bvalue t \/ nvalue t.
Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall t1,
      nvalue t1 ->
      (prd (scc t1)) --> t1
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall t1,
       nvalue t1 ->
      (iszro (scc t1)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')
where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step.

Notation step_normal_form := (normal_form step).
Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ not (value t).
Hint Unfold stuck.

(* some invalid exp *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (prd tru). unfold stuck.
  split. intros contra.
  destruct contra. inversion H; subst.
  inversion H1.
  intros contra.
  destruct contra; inversion H.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t Hval contra; inversion Hval;subst;
    induction H; inversion contra; subst;
      try inversion H0;subst;
        eauto;
        try inversion H;subst.
Qed.

Hint Resolve value_is_nf.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
Admitted.

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
Reserved Notation "'|-' t '∈' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru ∈ Bool
  | T_Fls :
       |- fls ∈ Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 ∈ Bool ->
       |- t2 ∈ T ->
       |- t3 ∈ T ->
       |- test t1 t2 t3 ∈ T
  | T_Zro :
       |- zro ∈ Nat
  | T_Scc : forall t1,
       |- t1 ∈ Nat ->
       |- scc t1 ∈ Nat
  | T_Prd : forall t1,
       |- t1 ∈ Nat ->
       |- prd t1 ∈ Nat
  | T_Iszro : forall t1,
       |- t1 ∈ Nat ->
       |- iszro t1 ∈ Bool
where "'|-' t '∈' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  |- test fls zro (scc zro) ∈ Nat.
Proof.
  apply T_Test.
    - apply T_Fls.
    - apply T_Zro.
    - apply T_Scc.
       + apply T_Zro.
Qed.

Example has_type_not :
  not( |- test fls zro tru ∈ Bool ).
Proof.
  intros Contra. solve_by_inverts 2. Qed.

Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t ∈ Nat ->
  |- t ∈ Nat.
Proof.
  intros. inversion H. assumption.
Qed.

