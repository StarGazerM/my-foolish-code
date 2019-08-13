Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Module STLCProp.
  Import STLC.

  Lemma canonical_forms_bool : forall t,
      empty |- t ∈ Bool ->
      value t ->
      (t = tru) \/ (t = fls).
  Proof.
    intros t HT HVal.
    inversion HVal; intros; subst; try inversion HT; auto.
  Qed.

  Lemma canonical_forms_fun : forall t T1 T2,
      empty |- t ∈ (Arrow T1 T2) ->
      value t ->
      exists x u, t = abs x T1 u.
  Proof.
    intros t T1 T2 HT HVal.
    inversion HVal; intros; subst; try inversion HT; subst; auto.
    exists x0, t0. auto.
  Qed.

  Theorem progress : forall t T,
      empty |- t ∈ T ->
              value t \/ exists t', t --> t'.
  Proof with eauto.
    intros t T Ht.
    remember (@empty ty) as Gamma.
    induction Ht; subst Gamma...
    - (* T_Var *)
      (* contradictory: variables cannot be typed in an
       empty context *)
      inversion H.
    - (* T_App *)
      (* t = t1 t2.  Proceed by cases on whether t1 is a
       value or steps... *)
      right.
      destruct IHHt1...
      + (* t1 is a value *)
        destruct IHHt2...
        * (* t2 is also a value *)
          assert (exists x0 t0, t1 = abs x0 T11 t0).
          eapply canonical_forms_fun; eauto.
          destruct H1 as [x0 [t0 Heq]]. subst.
          exists ([x0:=t2]t0)...
        * (* t2 steps *)
          inversion H0 as [t2' Hstp]. exists (app t1 t2')...
      + (* t1 steps *)
        inversion H as [t1' Hstp]. exists (app t1' t2)...
    - (* T_Test *)
      right. destruct IHHt1...
      + (* t1 is a value *)
        destruct (canonical_forms_bool t1); subst; eauto.
      + (* t1 also steps *)
        inversion H as [t1' Hstp]. exists(test t1' t2 t3)...
  Qed.

  Theorem progress' : forall t T,
      empty |- t ∈ T ->
      value t \/ exists t', t --> t'.
  Proof.
    intros t.
    induction t; intros T Ht; auto.
  Admitted.


  Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3).
  Hint Constructors appears_free_in.

  Definition closed (t:tm) :=
    forall x, not (appears_free_in x t).

  Lemma free_in_context : forall x t T Gamma,
      appears_free_in x t ->
      Gamma |- t ∈ T ->
              exists T', Gamma x = Some T'.
  Proof.
    intros x t T Gamma H H0. generalize dependent Gamma.
    generalize dependent T.
    induction H;
      intros; try solve [inversion H0; eauto].
    - (* afi_abs *)
      inversion H1; subst.
      apply IHappears_free_in in H7.
      rewrite update_neq in H7; assumption.
  Qed.

  Corollary typable_empty__closed : forall t T,
      empty |- t ∈ T ->
      closed t.
  Proof.
    unfold closed. intros.
    intros contra.
    apply free_in_context with (T:=T) (Gamma:=empty) in contra.
    inversion contra. inversion H0.
    assumption.
  Qed.

  Lemma context_invariance : forall Gamma Gamma' t T,
      Gamma |- t ∈ T ->
              (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
              Gamma' |- t ∈ T.
  Proof with eauto.
    intros.
    generalize dependent Gamma'.
    induction H; intros...
    - (* T_Var *)
      apply T_Var. rewrite <- H0...
    - (* T_Abs *)
      apply T_Abs.
      apply IHhas_type. intros x1 Hafi.
      (* the only tricky step... the Gamma' we use to
       instantiate is x⊢>T11;Gamma *)
      unfold update. unfold t_update. destruct (eqb_string x0 x1) eqn: Hx0x1...
      rewrite eqb_string_false_iff in Hx0x1. auto.
    - (* T_App *)
      apply T_App with T11...
  Qed.

  Lemma substitution_preserves_typing : forall Gamma x U t v T,
      (x |-> U ; Gamma) |- t ∈ T ->
      empty |- v ∈ U ->
              Gamma |- [x:=v]t ∈ T.
  Proof with eauto.
    intros Gamma x U t v T Ht Ht'.
    generalize dependent Gamma. generalize dependent T.
    induction t; intros T Gamma H;
      inversion H;subst;simpl...
    - (* var *)
      rename s into y.
      destruct (eqb_stringP x y) as [Hxy|Hxy].
      + (* y = x *)
        subst. rewrite update_eq in H2. inversion H2;subst.
        eapply context_invariance in Ht'.
        eassumption.
        intros. apply typable_empty__closed in Ht'.
        unfold closed in Ht'. eapply Ht' in H0. destruct H0.
      + (* y <> x*)
        Check update_neq.
        constructor. rewrite update_neq in H2...
    - (* abs *)
      rename s into y. rename t into T.
      destruct (eqb_stringP x y) as [Hxy|Hxy].
      + (* x = y *) subst.
        constructor.
        rewrite update_shadow in H5. assumption.
      + constructor.
        apply IHt. eapply context_invariance.
        eassumption.
        intros z Hafi. unfold update, t_update.
        destruct (eqb_stringP y z) as [Hyz|Hyz].
        rewrite <- eqb_string_false_iff in Hxy.
        subst. rewrite Hxy. auto.
        reflexivity.
  Qed.


  Theorem preservation : forall t t' T,
      empty |- t ∈ T ->
      t --> t' ->
      empty |- t' ∈ T.
  Proof with eauto.
    remember (@empty ty) as Gamma.
    intros t t' T HT. generalize dependent t'.
    induction HT;
      intros t' HE; subst Gamma; subst;
        try solve [inversion HE; subst; auto].
    - (* T_App *)
      inversion HE;subst...
      (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
      + (* ST_AppAbs *)
        apply substitution_preserves_typing with T11...
        inversion HT1...
  Qed.

  Definition stuck (t:tm) : Prop :=
    (normal_form step) t /\ not (value t).
  Corollary soundness : forall t t' T,
      empty |- t ∈ T ->
      t -->* t' ->
      not (stuck t').
  Proof with eauto.
    intros t t' T Hhas_type Hmulti. unfold stuck.
    intros [Hnf Hnot_val]. unfold normal_form in Hnf.
    induction Hmulti.
    apply progress in Hhas_type.
    destruct Hhas_type...
    apply preservation with (t':=y0) in Hhas_type...
  Qed.

  Theorem unique_types : forall Gamma e T T',
      Gamma |- e ∈ T ->
      Gamma |- e ∈ T' ->
      T = T'.
  Proof with eauto.
    intros.
    generalize dependent T. generalize dependent T'.
    generalize dependent Gamma.
    induction e;intros;
    inversion H;subst; clear H;
      inversion H0;subst; clear H0...
    - rewrite H2 in H3.
      inversion H3. auto.
    - apply IHe1 with Gamma (Arrow T11 T) (Arrow T0 T') in H4.
      apply IHe2 with Gamma T11 T0 in H6.
      subst. inversion H4. auto. auto. auto.
    - apply IHe with (s |-> t; Gamma) T12 T0 in H6.
      subst... auto.
  Qed.
  

End STLCProp.