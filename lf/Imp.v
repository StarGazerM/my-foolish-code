Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From LF Require Import Maps.

Module AExp.

  Inductive aexp: Type :=
  | ANum (n: nat)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult(a1 a2: aexp).

  Inductive bexp: Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2: aexp)
  | BLe (a1 a2: aexp)
  | BNot (b: bexp)
  | BAnd (b1 b2: bexp).

  Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

  Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

  Fixpoint optimize_0plus (a:aexp): aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a.
    - unfold optimize_0plus. reflexivity.
    - destruct a1 eqn:Ea1.
      + destruct n.
        * simpl. apply IHa2.
        * simpl. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa2.
        rewrite IHa1. reflexivity.
      + simpl. rewrite IHa2. simpl in IHa1.
        rewrite IHa1. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2.
      reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2.
      reflexivity.
  Qed.

  Lemma foo': forall n, 0 <=? n = true.
  Proof.
    intros.
    destruct n; simpl; reflexivity.
  Qed.

  (* if try fails just does nothing *)
  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof.
    try reflexivity. Qed.

  Theorem silly2: forall (P: Prop), P -> P.
  Proof.
    intros P HP.
    try reflexivity.
    apply HP. Qed.

  (* use try and ; to simplify our prove *)
  Theorem optimize_0plus_sound': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a;
      (* take care the case just rewrite IH*)
      try (simpl; rewrite IHa1; rewrite IHa2;
           reflexivity).
    - reflexivity.
    - destruct a1 eqn:Ea1;
        try (simpl; simpl in IHa1; rewrite IHa1;
             rewrite IHa2; reflexivity).
      + destruct n eqn:En;
          simpl; rewrite IHa2; reflexivity.
  Qed.

 Theorem optimize_0plus_sound'': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a;
      (* take care the case just rewrite IH*)
      try (simpl; rewrite IHa1; rewrite IHa2;
           reflexivity);
      try reflexivity.
    - destruct a1 eqn:Ea1;
        try (simpl; simpl in IHa1; rewrite IHa1;
             rewrite IHa2; reflexivity).
      + destruct n eqn:En;
          simpl; rewrite IHa2; reflexivity.
  Qed.

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  (* if fails just keep original goal *)
  Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try(left; reflexivity)).
  Qed.

  Fixpoint optimize_0plus_b (b: bexp): bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  Theorem optimize_0plus_b_sound: forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    intros.
    induction b;
      try reflexivity;
      try (simpl;
           repeat (rewrite optimize_0plus_sound);
           reflexivity).
    - simpl; rewrite IHb; reflexivity.
    - simpl; rewrite IHb1; rewrite IHb2;
        reflexivity.
  Qed.

  (* the newtype tool for tactic*)
  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl; try c.

  Example silly_presburger_example: forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega. Qed.

  Module avealR_first_try.

    (* evaluate from relation point of view*)

    Inductive aevalR: aexp -> nat -> Prop :=
    | E_ANum n:
        aevalR (ANum n) n
    | E_APlus (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat) :
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

    Module TooHardToRead.
      (* A small notational aside. We would previously have written the
   definition of aevalR like this, with explicit names for the
   hypotheses in each case: *)
      Inductive aevalR : aexp -> nat -> Prop :=
      | E_ANum n :
          aevalR (ANum n) n
      | E_APlus (e1 e2: aexp) (n1 n2: nat)
                (H1 : aevalR e1 n1)
                (H2 : aevalR e2 n2) :
          aevalR (APlus e1 e2) (n1 + n2)
      | E_AMinus (e1 e2: aexp) (n1 n2: nat)
                 (H1 : aevalR e1 n1)
                 (H2 : aevalR e2 n2) :
          aevalR (AMinus e1 e2) (n1 - n2)
      | E_AMult (e1 e2: aexp) (n1 n2: nat)
                (H1 : aevalR e1 n1)
                (H2 : aevalR e2 n2) :
          aevalR (AMult e1 e2) (n1 * n2).
      End TooHardToRead.


      Notation "e '\\' n"
        := (aevalR e n)
             (at level 50, left associativity)
           : type_scope.
      
    End avealR_first_try.
    Reserved Notation "e '\\' n" (at level 90, left associativity).

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum (n : nat) :
        (ANum n) \\ n
    | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
    | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
    | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
        (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

    where "e '\\' n" := (aevalR e n) : type_scope.

    Theorem aeval_iff_aevalR : forall a n,
        (a \\ n) <-> aeval a = n.
    Proof.
      (* WORKED IN CLASS *)
      split.
      - (* -> *)
        intros H; induction H; subst; reflexivity.
      - (* <- *)
        generalize dependent n.
        induction a; simpl; intros;
          subst; constructor;
            try apply IHa1;
            try apply IHa2; reflexivity.
    Qed.

    Inductive bevalR: bexp -> bool -> Prop :=
    | E_BTrue: bevalR BTrue true
    | E_BFalse: bevalR BFalse false
    | E_BEq (a1 a2: aexp) (e1 e2: nat):
        (aevalR a1 e1) -> (aevalR a2  e2) ->
        bevalR (BEq a1 a2) (e1 =? e2)
    | E_BLe (a1 a2: aexp) (e1 e2: nat):
        (aevalR a1 e1) -> (aevalR a2 e2) ->
        bevalR (BLe a1 a2) (e1 <=? e2)
    | E_BNot (b1: bexp) (e1: bool):
        (bevalR b1 e1) -> bevalR (BNot b1) (negb e1)
    | E_BAnd (b1 b2: bexp) (e1 e2: bool):
        (bevalR b1 e1) -> (bevalR b2 e2) ->
        bevalR (BAnd b1 b2) (andb e1 e2).

    Lemma beval_iff_bevalR : forall b bv,
        bevalR b bv <-> beval b = bv.
    Proof.
    (* FILL IN HERE *) Admitted.

    
    End AExp.

Module aevalR_division.
  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)

  Reserved Notation "e '\\' n"
           (at level 90, left associativity).
  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

  where "a '\\' n" := (aevalR a n) : type_scope.
  End aevalR_division.

Module aevalR_extended.

    Reserved Notation "e '\\' n" (at level 90, left associativity).
    Inductive aexp : Type :=
    | AAny (* <--- NEW *)
    | ANum (n : nat)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_Any (n : nat) :
        AAny \\ n (* <--- NEW *)
    | E_ANum (n : nat) :
        (ANum n) \\ n
    | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
    | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
    | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
        (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

    where "a '\\' n" := (aevalR a n) : type_scope.
End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId: string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope. 
Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Inductive com : Type :=
| CSkip
| CAss (x: string) (a: aexp)
| CSeq (c1 c2: com)
| CIf (b: bexp) (c1 c2: com)
| CWhile (b: bexp) (c: com).


Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.


Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

Unset Printing Notations.
Print fact_in_coq.

Set Printing Notations.

Locate "&&".

Locate aexp.

(* examples *)

Definition plus2: com :=
  X ::= X + 2.

Definition XtimeYinZ: com :=
  Z ::= X * Y.

Definition subtract_slowly_body: com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly: com :=
  (WHILE ~(X = 0) DO
         subtract_slowly_body
  END)%imp.

Definition subtract_3_from_5_slowly: com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly_body.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.


Reserved Notation "st '=[' c ']=>' st'"
         (at level 40).

Inductive ceval: com -> state -> state -> Prop :=
| E_Skip: forall st,
    st =[ SKIP ]=> st
| E_Ass: forall st a1 n x,
    aeval st a1 = n ->
    st =[ x ::= a1 ]=> (x !-> n ; st)
| E_Seq: forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ;; c2 ]=> st''
| E_IfTrue: forall st st' b1 c1 c2,
    beval st b1 = true ->
    st =[ c1 ]=> st' ->
    st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'
| E_IfFalse: forall st st' b1 c1 c2,
    beval st b1 = false ->
    st =[ c2 ]=> st' ->
    st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'
| E_WhileFalse: forall st b c,
    beval st b = false ->
    st =[ WHILE b DO c END ]=> st
| E_WhileTrue: forall st st' st'' b c,
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ WHILE b DO c END ]=> st'' ->
    st =[ WHILE b DO c END ]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Example ceval_example2:
  empty_st =[
    X ::= 0 ;; Y ::= 1 ;; Z ::= 2
  ]=> (Z !-> 2; Y !-> 1; X !-> 0).
Proof.
  eapply E_Seq.
  - apply E_Ass. reflexivity.
  - eauto.
Qed.

Ltac inv H := inversion H; subst; clear H.

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwinv H1 H2
  end.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
    intros st2 E2; inv E2; try find_rwinv;
      repeat find_eqn; auto.
Qed.

(* Theorem plus2_spec: forall st n st', *)
(*     st X = n -> *)
(*     st =[ plus2 ]=> st' -> *)
(*     st' X = n + 2. *)
(* Proof. *)
(*   intros st n st' HX Heval. *)
(*   simpl. *)

 

