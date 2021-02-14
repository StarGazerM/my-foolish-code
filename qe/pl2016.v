(* https://eng-cs.syr.edu/wp-content/uploads/2017/11/QE1_CISE_Jan16.pdf *)

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
| Mult (e1: expr) (e2: expr)
| Assign (x: string) (e1: expr)
| Clock (e1: expr).

Definition state := total_map nat.

(* original semantic *)
Inductive oeval : expr -> state -> nat -> state -> Prop :=
| OE_Num : forall σ n, oeval (Num n) σ n σ
| OE_Var : forall σ x, oeval (Var x) σ (σ x) σ
| OE_Inc : forall σ x, oeval (Inc x) σ (σ x) (x !-> ((σ x) + 1) ; σ)
| OE_Add : forall σ0 σ1 σ2 e1 e2 n1 n2,
    oeval e1 σ0 n1 σ1 ->
    oeval e2 σ1 n2 σ2 ->
    oeval (Plus e1 e2) σ0 (n1 + n2) σ2
| OE_Mult : forall σ0 σ1 σ2 e1 e2 n1 n2,
    oeval e1 σ0 n1 σ1 ->
    oeval e2 σ1 n2 σ2 ->
    oeval (Plus e1 e2) σ0 (n1 * n2) σ2.

(* cost is a int value *)
Inductive ceval : expr -> state -> nat -> state -> nat -> Prop :=
| CE_Num : forall σ n, ceval (Num n) σ n σ 0
| CE_Var : forall σ x, ceval (Var x) σ (σ x) σ 2
| CE_Inc : forall σ x, ceval (Inc x) σ (σ x) (x !-> ((σ x) + 1) ; σ) 3
| CE_Assign : forall σ0 σ1 x e n1 c1,
    ceval e σ0 n1 σ1 c1 ->
    ceval (Assign x e) σ1 n1 (x !-> n1 ; σ1) (c1 + 3)
| CE_Clock : forall σ0 σ1 e n1 c1,
    ceval e σ0 n1 σ1 c1 ->
    ceval (Clock e) σ1 n1 σ1 (n1 + c1)
| CE_Add : forall σ0 σ1 σ2 e1 e2 n1 n2 c1 c2,
    ceval e1 σ0 n1 σ1 c1 ->
    ceval e2 σ1 n2 σ2 c2 ->
    ceval (Plus e1 e2) σ0 (n1 + n2) σ2 (c1 + c2 + 1)
| CE_Mult : forall σ0 σ1 σ2 e1 e2 n1 n2 c1 c2,
    ceval e1 σ0 n1 σ1 c1 ->
    ceval e2 σ1 n2 σ2 c2 ->
    ceval (Plus e1 e2) σ0 (n1 * n2) σ2 (c1 + c2 + 1).


Hint Constructors oeval : core.
Hint Constructors ceval : core.


