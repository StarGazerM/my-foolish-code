Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import FunctionalExtensionality.
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
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption. Qed.


Theorem hoare_asgn_fwd:
  forall m a P,
    {{fun st => P st /\ st X = m}}
      X ::= a
    {{fun st => P (X !-> m ; st) /\
             st X = aeval (X !-> m ; st) a}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H; subst.
  destruct H0.
  rewrite t_update_shadow.
  rewrite <- H1. rewrite t_update_same.
  auto.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP.
  apply (Hhoare st st'). assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> 1]).
  apply hoare_asgn.
  intros st H.
  unfold assn_sub. auto.
Qed.

Theorem hoare_consequence : forall(P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption. Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Definition swap_program : com :=
  Z ::= AId X ;; X ::= AId Y ;; Y ::= AId Z.

Theorem swap_ex:
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq. eapply hoare_seq.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H. eauto.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H. eauto.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H. eauto.
Qed.

(* lift of bool *)
Definition bassn b: Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
    beval st b = true -> (bassn b) st.
Proof.
  intros. unfold bassn. apply H.
Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> not ((bassn b) st).
Proof.
  intros. unfold bassn.
  rewrite H. auto. Qed.

Hint Unfold bassn.
Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ not (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros.
  intros st st' HE HP.
  inversion HE; subst.
  apply (H st); auto.
  apply (H0 st); auto.
  split. assumption. unfold bassn.
  rewrite H6. auto.
Qed.

Example if_example :
    {{fun st => True}}
  TEST X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply eqb_eq in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub, assert_implies, t_update.
    simpl; intros st [_ Ht].
    Search (_ = _ + (_ - _)).
    Search (_ <=? _ = true).
    apply leb_le in Ht.
    apply le_plus_minus. assumption.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub, assert_implies, t_update.
    simpl. auto.
Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ not (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END)%imp as wcom.
  induction He;
    try (inversion Heqwcom); subst.
  - split. assumption. unfold bassn.
    apply bexp_eval_false. assumption.
  - apply IHHe2. assumption.
    apply (Hhoare st). assumption.
    split. assumption. apply bexp_eval_true. assumption.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor. Qed.







