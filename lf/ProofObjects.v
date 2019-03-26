Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

(* normal tactical proof *)
Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(* function way *)
Definition ev_plus4': forall n, even n -> even(4+n):=
  fun (n: nat) => fun (H: even n) =>
                ev_SS (S (S n)) (ev_SS n H).

(* define value *)
Definition ev_plus4'' (n: nat)(H: even n)
  : even (4+n) :=
  ev_SS (S (S n)) (ev_SS n H).

(* imply -> is actually the same as forall*)
Definition ev_plus2: Prop :=
  forall n, forall (E: even n), even (n+2).

Definition ev_plus2': Prop :=
  forall n, even n -> even (n+2).

Definition add1: nat -> nat.
  intros n.
  apply n. Defined.

Module Props.

  Module And.

    Inductive and (P Q:Prop): Prop :=
      | conj: P -> Q -> and P Q.
    End And.

    Lemma and_common: forall P Q: Prop, P /\ Q <-> Q /\ P.
    Proof.
      intros P Q. split.
      - intros [HP HQ]. split.
        apply HQ. apply HP.
      - intros [HQ HP]. split.
        apply HP. apply HQ.
    Qed.

    Definition and_comm'_aux P Q (H: P /\ Q) :=
      match H with
      | conj HP HQ => conj HQ HP
      end.

    Definition conj_fact: forall P Q R,
        P /\ Q -> Q /\ R -> P /\ R. Admitted.

    Module Or.
      Inductive or (P Q : Prop) : Prop :=
      | or_introl : P -> or P Q
      | or_intror : Q -> or P Q.
      End Or.

      Definition or_comm : forall P Q, P \/ Q -> Q \/ P.
      Admitted.

    Module Ex.
      Inductive ex {A : Type} (P : A -> Prop) : Prop :=
      | ex_intro : forall x : A, P x -> ex P.
      End Ex.

      Definition some_nat_is_even : exists n, even n :=
        ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

    Inductive True : Prop :=
    | I : True.

    Inductive False : Prop :=.

  End Props.

  Module MyEquality.

    Inductive eq {X: Type}: X -> X -> Prop :=
    | eq_refl: forall x, eq x x.

    Notation "x == y" := (eq x y)
                           (at level 70,no associativity)
                         : type_scope.

    Lemma equality_leibniz_equlity: forall (X: Type) (x y: X),
        x == y -> forall P:X -> Prop, P x -> P y.
    Proof.
      intros.
      destruct H. apply H0.
    Qed.

    (* equlity we defined is already leibniz equlity*)
    Lemma leibniz_equality_equality: forall (X: Type) (x y: X),
        (forall P: X -> Prop, P x -> P y) -> x == y.
    Proof.
      intros.
      apply (H (fun z => x == z)).
      apply eq_refl.
    Qed.

    End MyEquality.