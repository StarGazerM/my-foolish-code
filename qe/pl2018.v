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

Inductive expr : Type :=
| Tru
| Fls
| If (e0 : expr) (e1 : expr) (e2 : expr)
| Raise (γ : string)
| Handle (e1 : expr) (γ : string) (e2 : expr).

(* bool is the only type here *)
Inductive ty : Type :=
| TBool : ty.

Inductive eval : expr -> expr -> Prop :=
| E_If_t : forall e2 e3, eval (If Tru e2 e3) e2
| E_If_f : forall e2 e3, eval (If Fls e2 e3) e3
| E_If_g : forall e1 e1' e2 e3,
    eval e1 e1' ->
    eval (If e1 e2 e3) (If e1' e2 e3)
| E_If_r : forall e2 e3 γ,
    eval (If (Raise γ) e2 e3) (Raise γ)
| E_handle_t : forall γ e2, eval (Handle Tru γ e2) Tru
| E_handle_f : forall γ e2, eval (Handle Fls γ e2) Fls
| E_handle_r : forall γ e2, eval (Handle (Raise γ) γ e2) e2
| E_handle_e : forall e1 e1' γ e2,
    eval e1 e1' ->
    eval (Handle e1 γ e2) (Handle e1' γ e2)
| E_handle_h : forall γ γ' e2,
    γ <> γ' ->
    eval (Handle (Raise γ) γ' e2) (Raise γ).

Definition context := total_map nat.

Inductive value : expr -> Prop :=
| v_t : value Tru
| v_f : value Fls.

Inductive has_type : context -> expr -> ty -> Prop :=
| T_Tru : forall Γ, has_type Γ Tru TBool
| T_Fls : forall Γ, has_type Γ Fls TBool
| T_Raise : forall Γ γ, (Γ γ) = 1 -> has_type Γ (Raise γ) TBool
| T_If : forall Γ e1 e2 e3,
    has_type Γ e1 TBool ->
    has_type Γ e2 TBool ->
    has_type Γ e3 TBool ->
    has_type Γ (If e1 e2 e3) TBool
| T_Handle : forall Γ γ e1 e2,
    (Γ γ) = 0 ->
    has_type (γ !-> 1 ; Γ) e1 TBool ->
    has_type Γ e2 TBool ->
    has_type Γ (Handle e1 γ e2) TBool.

Hint Constructors eval : core.
Hint Constructors has_type : core.
Hint Constructors value : core.

Local Open Scope string_scope.

Theorem e_progress : forall e T Γ,
    has_type Γ e T ->
    value e \/ (exists γ, (Γ γ) = 1 -> e = Raise γ) \/ exists e', eval e e'.
Proof with eauto.
  intros.
  induction H...
  - inversion H; subst...
    destruct IHhas_type1. inversion H5.
    destruct H5. destruct H5.
    right. left. exists x. intros. apply H5 in H6. discriminate H6.
    right. right. destruct H5...
    destruct IHhas_type1. inversion H5.
    destruct H5. destruct H5.
    right. left. exists x. intros. apply H5 in H6. discriminate H6.
    right. right. destruct H5...
  - inversion H0; subst...
    destruct IHhas_type1. inversion H3.
    destruct H3. destruct H3.
    (* need some related to string eqb *)
    Admitted.


(* Theorem e_progress : forall e T Γ, *)
(*     has_type Γ e T -> *)
(*     value e \/ (exists γ, e = Raise γ) \/ exists e', eval e e'. *)
(* Proof with eauto. *)
(*   intros. *)
(*   induction H... *)
(*   - right. right. *)
(*     destruct IHhas_type1. *)
(*     inversion H2... *)
(*     destruct H2. destruct H2. *)
(*     inversion H; subst... *)
(*     discriminate H7. *)
(*     discriminate H7. *)
(*     destruct H2... *)
(*   - right. right. *)
(*     destruct IHhas_type1. *)
(*     inversion H2; subst... *)
(*     destruct H2. *)
(*     destruct H2. *)
(*     inversion H0; subst... *)
(*     rewrite <- H5 in H0. *)
(*     exists (Raise γ0). constructor. *)
    



