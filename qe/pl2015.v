(*  2015 SU QE https://eng-cs.syr.edu/wp-content/uploads/2017/11/QE1_CISE_Jan15.pdf
 *  Yihao Sun
 *  Syracuse 2021
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From QE Require Import Maps.

Inductive expr : Type  :=
| Num (n: nat)
| Var (x: string)
| Inc (x: string)
| Plus (e1: expr) (e2: expr)
| Pick (e1: expr) (e2: expr).

Definition state := total_map nat.

(* original semantic *)
Inductive oeval : expr -> state -> nat -> state -> Prop :=
| OE_Num : forall σ n, oeval (Num n) σ n σ
| OE_Var : forall σ x, oeval (Var x) σ (σ x) σ
| OE_Inc : forall σ x, oeval (Inc x) σ (σ x) (x !-> ((σ x) + 1) ; σ)
| OE_Add1 : forall σ0 σ1 σ2 e1 e2 n1 n2,
    oeval e1 σ0 n1 σ1 ->
    oeval e2 σ1 n2 σ2 ->
    oeval (Plus e1 e2) σ0 (n1 + n2) σ2
| OE_Choice1 : forall e1 σ n1 σ1 e2 n2 σ2,
    oeval e1 σ n1 σ1 ->
    oeval e2 σ n2 σ2 ->
    oeval (Pick e1 e2) σ n1 σ1
| OE_Choice2 : forall e1 σ n1 σ1 e2 n2 σ2,
    oeval e1 σ n1 σ1 ->
    oeval e2 σ n2 σ2 ->
    oeval (Pick e1 e2) σ n2 σ2.

Inductive aeval : expr -> state -> nat -> state -> Prop :=
| AE_Num : forall σ n, aeval (Num n) σ n σ
| AE_Var : forall σ x, aeval (Var x) σ (σ x) σ
| AE_Inc : forall σ x, aeval (Inc x) σ (σ x) (x !-> ((σ x) + 1) ; σ)
| AE_Add : forall σ0 σ1 σ2 e1 e2 n1 n2,
    aeval e1 σ0 n1 σ1 ->
    aeval e2 σ1 n2 σ2 ->
    aeval (Plus e1 e2) σ0 (n1 + n2) σ2
| AE_Choice1 : forall e1 σ n1 σ1 e2 n2 σ2,
    aeval e1 σ n1 σ1 ->
    aeval e2 σ n2 σ2 ->
    aeval (Pick e1 e2) σ n1 σ2
| AE_Choice2 : forall e1 σ n1 σ1 e2 n2 σ2,
    aeval e1 σ n1 σ1 ->
    aeval e2 σ1 n2 σ2 ->
    aeval (Pick e1 e2) σ n2 σ2.

Hint Constructors oeval : core.
Hint Constructors aeval : core.

Theorem original_alter_eq_exists: forall e σ n σ',
    oeval e σ n σ' ->
    exists σ'', aeval e σ n σ''.
Proof with eauto.
  intros.
  induction H...
  - subst.
    destruct IHoeval1 as [σ3 IHa1]. destruct IHoeval2 as [σ4 IHa2].


    inversion IHa1; subst; inversion IHa2; subst; inversion H; subst; inversion H0; subst...
    + rewrite H6...
    + rewrite H5...
    + rewrite H5...
    + rewrite H5...
    + rewrite H5...
      Abort.



