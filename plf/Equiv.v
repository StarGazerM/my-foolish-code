Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From PLF Require Import Imp.

Definition aequiv (a1 a2: aexp): Prop :=
  forall (st: state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2: bexp): Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Theorem aequiv_example: aequiv (X - X) 0.
Proof.
  intros st. 
  simpl.
  omega.
Qed.

Print bequiv.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  simpl. reflexivity.
Qed.

Definition cequiv (c1 c2: com): Prop :=
  forall (st st': state),
    (st =[ c1 ]=> st') <->
    (st =[ c2 ]=> st').

Check E_Seq.

Theorem skip_left: forall c,
    cequiv
      (SKIP;; c)
      c.
Proof.
  intros c st st'.
  split.
  intros H.
  - inversion H.
    inversion H; subst.
    inversion H2; subst.
    assumption.
  - Check E_Seq.
    apply E_Seq. apply E_Skip.
Qed.

Theorem skip_right : forall c,
    cequiv
      (c ;; SKIP)
      c.
Proof.
  unfold cequiv.
  intros.
  split.
  - intros H.
    inversion H; subst.
    inversion H5; subst.
    apply H2.
  - intros H.
    Check E_Seq.
    apply E_Seq with st'. apply H.
    apply E_Skip.
Qed.

Theorem TEST_true_simple: forall c1 c2,
    cequiv
      (TEST true THEN c1 ELSE c2 FI)
      c1.
Proof.
  intros.
  split. intros H.
  inversion H; subst. assumption.
  discriminate H5.
  apply E_IfTrue. auto.
Qed.


Theorem  TEST_true: forall b c1 c2,
    bequiv b BTrue ->
    cequiv
      (TEST b THEN c1 ELSE c2 FI)
      c1.
Proof.
  unfold bequiv.
  simpl.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H. subst.
    assumption.
    rewrite Hb in H5. inversion H5.
  - apply E_IfTrue. apply Hb.
    auto.
Qed.

Theorem TEST_false: forall b c1 c2,
    bequiv b BFalse ->
    cequiv
      (TEST b THEN c1 ELSE c2 FI)
      c2.
Proof.
  unfold bequiv.
  simpl.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst.
    + rewrite Hb in H5.
      inversion H5.
    + assumption.
  - apply E_IfFalse; auto.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity.  Qed.


Lemma WHILE_true_nonterm: forall b c st st',
    bequiv b BTrue ->
    ~(st =[ WHILE b DO c END ]=> st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H;
    inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb.
    rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity.
Qed.


Theorem WHILE_true: forall b c,
    bequiv b true ->
    cequiv
      (WHILE b DO c END)
      (WHILE true DO SKIP END).
Proof.
  intros b c Hb.
  split; intros.
  inversion H; subst. unfold bequiv in Hb.
  rewrite Hb in H4. inversion H4.
  apply WHILE_true_nonterm with b c st st' in Hb.
  contradiction.
  assert (~(st =[ WHILE true DO SKIP END ]=> st')).
  apply WHILE_true_nonterm.
  unfold bequiv. auto.
  contradiction.
Qed.

Theorem seq_assoc: forall c1 c2 c3,
    cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3)).
Proof.
  intros.
  split; intros.
  inversion H; subst.
  inversion H2; subst.
  apply E_Seq with st'1; auto.
  apply E_Seq with st'0; auto.
  inversion H; subst.
  inversion H5; subst.
  apply E_Seq with st'1.
  apply E_Seq with st'0; auto.
  auto.
Qed.


Theorem identity_assignment : forall x,
  cequiv
    (x ::= x)
    SKIP.
Proof.
  intros.
  split; intro H; inversion H; subst.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x ::= x ]=> (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

Theorem assign_aequiv : forall(x : string) e,
  aequiv x e ->
  cequiv SKIP (x ::= e).
Proof.
  intros x e Ha.
  split; intros; unfold aequiv in Ha; inversion H; subst.
  assert (Hx : st' =[ x ::= e ]=> (x !-> st' x ; st')).
  apply E_Ass. eauto.
  rewrite t_update_same in Hx.
  auto.
  rewrite <- Ha. rewrite t_update_same.
  apply E_Skip.
Qed.

Definition prog_a : com :=
  (WHILE ~(X <= 0) DO
    X ::= X + 1
  END)%imp.
Definition prog_b : com :=
  (TEST X = 0 THEN
    X ::= X + 1;;
    Y ::= 1
  ELSE
    Y ::= 0
  FI;;
  X ::= X - Y;;
  Y ::= 0)%imp.
Definition prog_c : com :=
  SKIP%imp.
Definition prog_d : com :=
  (WHILE ~(X = 0) DO
    X ::= (X * Y) + 1
  END)%imp.
Definition prog_e : com :=
  (Y ::= 0)%imp.
Definition prog_f : com :=
  (Y ::= X + 1;;
  WHILE ~(X = Y) DO
    Y ::= X + 1
  END)%imp.
Definition prog_g : com :=
  (WHILE true DO
    SKIP
  END)%imp.
Definition prog_h : com :=
  (WHILE ~(X = X) DO
    X ::= X + 1
  END)%imp.
Definition prog_i : com :=
  (WHILE ~(X = Y) DO
    X ::= Y + 1
  END)%imp.
Definition equiv_classes : list (list com)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.

Lemma refl_aequiv : forall (a: aexp), aequiv a a.
Proof. intros a st. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
      aequiv a1 a2 -> aequiv a2 a1.
Proof.
   intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
      aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
   unfold aequiv. intros a1 a2 a3 H12 H23 st.
   rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
   unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
      bequiv b1 b2 -> bequiv b2 b1.
Proof.
   unfold bequiv. intros b1 b2 H. intros st.
   symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
      bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
   unfold bequiv. intros b1 b2 b3 H12 H23 st.
   rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_cequiv: forall (c : com), cequiv c c.
Proof.
   unfold cequiv. intros c st st'. apply iff_refl. Qed.

Lemma sym_cequiv: forall (c1 c2 : com),
      cequiv c1 c2 -> cequiv c2 c1.
Proof.
   unfold cequiv. intros c1 c2 H st st'.
   assert(st =[ c1 ]=> st' <-> st =[ c2 ]=> st') as H'.
   apply H.
   apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
      (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
      intros P1 P2 P3 H12 H23.
      inversion H12. inversion H23.
      split; intros A.
         apply H1. apply H. apply A.
         apply H0. apply H2. apply A. Qed.

Lemma trans_cequiv: forall (c1 c2 c3 : com),
      cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
   unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
   apply iff_trans with (st =[ c2 ]=> st'). apply H12. apply H23. Qed.


Theorem CAss_congruence : forall x a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss x a1) (CAss x a1').
Proof.
  intros.
  split; intros;
  inversion H0; subst;
  unfold aequiv in H.
  - rewrite H.
    apply E_Ass. auto.
  - rewrite <- H.
    apply E_Ass. auto.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END)%imp as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END)%imp as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
(* FILL IN HERE *) Admitted.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (TEST b THEN c1 ELSE c2 FI)
         (TEST b' THEN c1' ELSE c2' FI).
Proof.
  intros.
  split; intros;
    unfold bequiv in H; unfold cequiv in H0; unfold cequiv in H1;
    inversion H2; subst.
  - apply E_IfTrue. rewrite <- H. auto.
    rewrite <- H0. auto.
  - apply E_IfFalse. rewrite <- H. auto.
    rewrite <- H1. auto.
  - apply E_IfTrue. rewrite H. auto.
    rewrite H0. auto.
  - apply E_IfFalse. rewrite H. auto.
    rewrite H1. auto.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    (* Program 2: *)
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= X - X (* <--- Changed here *)
     ELSE
       Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      * symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall(a : aexp),
    aequiv a (atrans a).
Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall(b : bexp),
    bequiv b (btrans b).
Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall(c : com),
    cequiv c (ctrans c).

(* constants folding *)

Fixpoint fold_constants_aexp (a: aexp): aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp ((1 + 2) * X) 
  = (3 * X)%imp.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Open Scope imp.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | x ::= a =>
      x ::= (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound.
  unfold aequiv. intros.
  induction a; simpl; auto;
    destruct (fold_constants_aexp a1);
    destruct (fold_constants_aexp a2); simpl; auto.
Qed.

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_nat_true_iff.
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

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
        (subst a1'; rewrite <- fold_constants_aexp_sound; auto).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; auto).
    destruct a1'; destruct a2'; auto. simpl.
    bdestruct (n <=? n0). induction n; auto. simpl. auto.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.


Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* TEST *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply TEST_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply TEST_false; assumption.
  - (* WHILE *)
    remember (fold_constants_bexp b) as b'.
    assert (bequiv b b').
    rewrite Heqb'. apply fold_constants_bexp_sound.
    destruct b';
      (* some thing happened here so I can't finish this in auto *)
      try (apply CWhile_congruence;assumption; assumption).
    apply WHILE_true. assumption.
    apply WHILE_false. assumption.
Qed.

Fixpoint optimize_0plus (e:aexp) : aexp :=
  match e with
  | AId n => AId n
  | ANum n =>
    ANum n
  | APlus (ANum 0) e2 =>
    optimize_0plus e2
  | APlus e1 e2 =>
    APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
    AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
    AMult (optimize_0plus e1) (optimize_0plus e2)
  end.


Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId x' =>
      if eqb_string x x' then u else AId x'
  | APlus a1 a2 =>
      APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

Theorem subst_inequiv:
  not subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  remember (X ::= X + 1 ;; Y ::= X)%imp as c1.
  remember (X ::= X + 1 ;; Y ::= X + 1)%imp as c2.
  assert (cequiv c1 c2).
  { subst; apply Contra. }
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  apply H in H1.
  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.
Qed.

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMult a1 a2).
Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros.
  induction H; simpl; try auto.
  apply t_update_neq. assumption.
Qed.

(* Lemma subst_aexp_weak : forall x a1 a2, *)
(*     var_not_used_in_aexp x a1 -> *)
(*     x  *)


Theorem subst_equiv : forall x1 x2 a1 a2,
   var_not_used_in_aexp x1 a1 ->
     cequiv (x1 ::= a1 ;; x2 ::= a2)
         (x1 ::= a1 ;; x2 ::= subst_aexp x1 a1 a2).
Proof.
  split; intros.
  remember (subst_aexp x1 a1 a2) as subx1.
  inversion H0; subst.
  apply E_Seq with (st' := st'0).
  assumption.
Admitted.






