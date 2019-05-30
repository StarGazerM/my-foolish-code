Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm (* Constant *)
  | P : tm -> tm -> tm. (* Plus *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).
Module SimpleArith1.
  Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
where " t '-->' t' " := (step t t').

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst. Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  repeat apply ST_Plus2. apply ST_PlusConstConst. Qed.

End SimpleArith1.

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
  Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst. reflexivity.
    inversion H2; subst. inversion H2; subst.
  - inversion Hy2; subst.
    inversion Hy1. (* imposible case for different type of y1 and y2*)
    rewrite (IHHy1 t1'0). reflexivity. assumption.
    inversion Hy1. (* imposible *)
  - inversion Hy2; subst.
    inversion Hy1. (* imposible*)
    inversion H2. (* imposible *)
    rewrite (IHHy1 t2'0). reflexivity. assumption.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.
Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.
End SimpleArith3.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).
 
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'
where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2;subst. reflexivity.
    inversion H2.
    inversion H3.
  - inversion Hy2; subst. inversion Hy1.
    rewrite (IHHy1 t1'0). reflexivity. assumption.
    inversion Hy1; subst. inversion H1. (* both has the form P t11 t12 and is a value (hence has the form C n). *)
    inversion H1.
    rewrite (IHHy1 t0). inversion H1.
    inversion H1.
  - inversion Hy2; subst. inversion Hy1; subst.
    inversion H3; subst; inversion H.
    rewrite (IHHy1 t2'0). reflexivity. assumption.
Qed.

Theorem strong_progress : forall t,
    value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. apply v_const.
  - right. destruct IHt1.
    + destruct IHt2.
      inversion H; subst. inversion H0; subst.
      exists (C (n + n0)). apply ST_PlusConstConst.
      destruct H0.
      exists (P t1 x).
      apply ST_Plus2. assumption. assumption.
    + destruct H; destruct IHt2;
        exists (P x t2); apply ST_Plus1; assumption.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  not (exists t', R t t').

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of strong_progress... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

Module Temp1.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2,
                value (P t1 (C n2)). (* <--- *)
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ not (normal_form step v).
Proof.
  (* FILL IN HERE *) Admitted.
End Temp1.

Module Temp4.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

where " t '-->' t' " := (step t t').

Definition bool_step_prop1 :=
  fls --> fls.

Theorem not_bool_step_prop1:
  not bool_step_prop1.
Proof.
  unfold bool_step_prop1.
  intros contra. inversion contra. Qed.

Definition bool_step_prop2 :=
     test
       tru
       (test tru tru tru)
       (test fls fls fls)
  -->
  tru.

Theorem not_bool_step_prop2:
  not bool_step_prop2.
Proof.
  intros contra. inversion contra.
Qed.

Definition bool_step_prop3 :=
     test
       (test tru tru tru)
       (test tru tru tru)
       fls
   -->
     test
       tru
       (test tru tru tru)
       fls.

Theorem true_bool_step_prop3 :
  bool_step_prop3.
Proof.
  unfold bool_step_prop3. constructor. constructor.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - left. apply v_tru.
  - left. apply v_fls.
  - right.
    destruct IHt1. inversion H; subst.
    exists t2. apply ST_IfTrue.
    exists t3. apply ST_IfFalse.
    destruct H.
    exists (test x t2 t3). apply ST_If. assumption.
Qed.

Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2;subst. reflexivity.
    inversion H3.
  - inversion Hy2; subst. reflexivity.
    inversion H3.
  - inversion Hy2; subst.
    inversion Hy1.
    inversion Hy1.
    rewrite (IHHy1 t1'0). reflexivity. assumption.
Qed.

Module Temp5.

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  | ST_Short : forall t1 t2 ,
      test t1 t2 t2 --> t2
where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
         test
            (test tru tru tru)
            fls
            fls
     -->
     fls.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  unfold bool_step_prop4. apply ST_Short. Qed.

End Temp5.
End Temp4.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_Plus1. apply ST_PlusConstConst. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
  apply multi_R.
  { apply ST_PlusConstConst. }
Qed.

Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
Qed.

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  apply multi_refl. Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  apply multi_refl. Qed.


Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply multi_step. apply ST_Plus2. constructor.
  apply ST_Plus2. constructor. constructor.
  eapply multi_step. simpl.
  apply ST_Plus2. constructor. constructor.
  simpl.
  apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  induction P11; intros.
  destruct x.
  inversion P21; subst. reflexivity.
  inversion H; subst.
  apply nf_is_value in P12. inversion P12.
  apply IHP11.
  assumption.
  inversion P21; subst.
Admitted.

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
      (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     P t1 t2 -->* P t1 t2'.
Proof.
  intros.
  induction H0.
  - apply multi_refl.
  - apply multi_step with (P t1 y).
    apply ST_Plus2. assumption.
    assumption.
    assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use rewrite with "iff" statements, not
           just equalities: *)
      rewrite nf_same_as_value. apply v_const.
  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1]].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2]].
    rewrite nf_same_as_value in Hnormal1.
    rewrite nf_same_as_value in Hnormal2.
    inversion Hnormal1 as [n1 H1].
    inversion Hnormal2 as [n2 H2].
    rewrite <- H1 in Hsteps1.
    rewrite <- H2 in Hsteps2.
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with
        (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. { apply ST_PlusConstConst. }
    + (* r *)
      rewrite nf_same_as_value. apply v_const.
Qed.

Theorem eval__multistep : forall t n,
    t ==> n -> t -->* C n.
Proof.
  intros.
  induction H.
  apply multi_refl.
  apply multi_trans with (P (C n1) t2).
  apply multistep_congr_1. assumption.
  apply multi_trans with (P (C n1) (C n2)).
  apply multistep_congr_2. apply v_const. assumption.
  eapply multi_R. apply ST_PlusConstConst.
Qed.

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros.
  - inversion H; subst.
    constructor. constructor.
    constructor.
  - inversion H; subst.
    constructor. apply IHHs. assumption.
    assumption.
  - inversion H; subst.
    inversion H0; subst.
    constructor. assumption.
    apply IHHs. assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  intros.
  destruct H.
  induction H.
  apply nf_is_value in H0.
  inversion H0;subst. exists n.
  split. reflexivity. constructor.
  apply  IHmulti in H0.
  destruct H0 as [n [Hz Hp]]. exists n.
  inversion H; subst; split;
    try reflexivity;
    try eapply step__eval; eassumption; eassumption.
Qed.



