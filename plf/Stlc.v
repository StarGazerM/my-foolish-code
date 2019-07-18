Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Module STLC.

  (* type *)
  Inductive ty : Type :=
  | Bool: ty
  | Arrow: ty -> ty -> ty.

  (* term *)
  Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

  Open Scope string_scope.

  Definition x := "x".
  Definition y := "y".
  Definition z := "z".
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.

  (* idB = \x:Bool. x *)
  Notation idB :=
    (abs x Bool (var x)).

  (* idBB = \x:Bool→Bool. x *)
  Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

  (* idBBB = \x:(Bool -> Bool) -> (Bool -> Bool). x*)
  Notation idBBBB :=
    (abs x (Arrow (Arrow Bool Bool)
                  (Arrow Bool Bool))
         (var x)).

  (* k = \x:Bool. \y:Bool. x *)
  Notation k := (abs x Bool (abs y Bool (var x))).

  (* notB = \x:Bool. test x then fls else tru *)
  Notation notB := (abs x Bool (test (var x) fls tru)).

  Compute (fun x:bool => 3 + 4).

  Inductive value: tm -> Prop:=
  | v_abs: forall x T t,
      value (abs x T t)
  | v_tru:
      value tru
  | v_fls:
      value fls.

  Hint Constructors value.

  Reserved Notation "'[' x ':=' s ']' t" (at level 20).
  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    | var x' =>
          if eqb_string x x' then s else t
    | abs x' T t1 =>
          abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
    | app t1 t2 =>
          app ([x:=s] t1) ([x:=s] t2)
    | tru =>
          tru
    | fls =>
          fls
    | test t1 t2 t3 =>
           test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
    end

  where "'[' x ':=' s ']' t" := (subst x s t).

  Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2: forall x',
      x <> x' ->
      substi s x (var x') (var x')
  | s_abs1 : forall T t1,
      substi s x (abs x T t1) (abs x T t1)
  | s_abs2 : forall x' T t1 t2,
      x <> x' ->
      substi s x t1 t2 ->
      substi s x (abs x' T t1) (abs x' T t2)
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru :
      substi s x tru tru
  | s_fls :
      substi s x fls fls
  | s_test : forall t1 t2 t3 t1' t2' t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (test t1 t2 t3) (test t1' t2' t3').

  Hint Constructors substi.
  Hint Resolve eqb_string_true_iff.
  Hint Resolve eqb_string_false_iff.

  Theorem substi_correct : forall s x t t',
      [x:=s] t = t' <-> substi s x t t'.
  Proof with auto.
    split; intros.
    - generalize dependent t'.
      induction t.
      simpl. remember (eqb_string x0 s0) as eqbXS;
      symmetry in HeqeqbXS;
      destruct eqbXS.
      Search (eqb_string _ _). 
      apply eqb_string_true_iff in HeqeqbXS.
      intros; subst; auto.
      apply eqb_string_false_iff in HeqeqbXS.
      intros; subst; auto.
      intros; subst; try constructor; auto.
      simpl. remember (eqb_string x0 s0) as eqbXS;
      symmetry in HeqeqbXS;
      destruct eqbXS.
      apply eqb_string_true_iff in HeqeqbXS.
      intros. subst. auto.
      apply eqb_string_false_iff in HeqeqbXS.
      intros. subst. auto.
      intros; subst; try constructor; auto.
      intros; subst; try constructor; auto.
      intros; subst; try constructor; auto.
    - induction H; simpl; auto;
        try rewrite <- eqb_string_refl; auto;
          try rewrite false_eqb_string; subst; auto.
  Qed.

  Reserved Notation "t1 '-->' t2" (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1 t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

  where "t1 '-->' t2" := (step t1 t2).

  Hint Constructors step.
  Notation multistep := (multi step).
  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

  Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
  Tactic Notation "normalize" :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
    apply multi_refl.
  Lemma step_example5:
    app (app idBBBB idBB) idB -->* idB.
  Proof.
    eapply multi_step.
    repeat constructor.
    eapply multi_step.
    repeat constructor.
    constructor.
  Qed.

  Definition context := partial_map ty.

  Reserved Notation "Gamma '|-' t '∈' T" (at level 40).
  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x ∈ T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 ∈ T12 ->
      Gamma |- abs x T11 t12 ∈ Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 ∈ Arrow T11 T12 ->
      Gamma |- t2 ∈ T11 ->
      Gamma |- app t1 t2 ∈ T12
  | T_Tru : forall Gamma,
      Gamma |- tru ∈ Bool
  | T_Fls : forall Gamma,
      Gamma |- fls ∈ Bool
  | T_Test : forall t1 t2 t3 T Gamma,
      Gamma |- t1 ∈ Bool ->
      Gamma |- t2 ∈ T ->
      Gamma |- t3 ∈ T ->
      Gamma |- test t1 t2 t3 ∈ T

  where "Gamma '|-' t '∈' T" := (has_type Gamma t T).
  Hint Constructors has_type.

  Example typing_example_1 :
    empty |- abs x Bool (var x) ∈ Arrow Bool Bool.
  Proof.
    apply T_Abs. apply T_Var. reflexivity. Qed.


  Example typing_example_2_full :
    empty |-
          (abs x Bool
               (abs y (Arrow Bool Bool)
                    (app (var y) (app (var y) (var x))))) ∈
          (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
  Proof. 
    apply T_Abs. apply T_Abs.
    eapply T_App.
    apply T_Var. reflexivity.
    eapply T_App. apply T_Var. reflexivity.
    apply T_Var. reflexivity.
  Qed.


  (*  ¬∃T,
        empty ⊢ \x:Bool. \y:Bool, x y ∈ T. *)
  Example typing_nonexample_1 :
    not (exists T,
        empty |-
        (abs x Bool
             (abs y Bool
                  (app (var x) (var y)))) ∈
                                          T).
  Proof.
    intros Hc. inversion Hc.
    (* The clear tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H5. subst. clear H5.
    inversion H1. Qed.

Example typing_nonexample_3 :
  not (exists S T,
        empty |-
          (abs x S
             (app (var x) (var x))) ∈
          T).
Proof.
  unfold not. intros. inversion H. clear H. inversion H0. clear H0.
  inversion H;subst; clear H.
  inversion H5; subst. clear H5.
  inversion H2;subst. clear H2.
  inversion H4;subst. clear H4.
  rewrite -> H2 in H1. inversion H1. clear H1 H2.
  generalize dependent T12. induction T11.
  + intros. inversion H0.
  + intros. inversion H0;subst. eapply IHT11_1. eauto. Qed.

End STLC.


      

      

  
