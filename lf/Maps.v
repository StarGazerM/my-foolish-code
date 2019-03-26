From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl: forall s: string,
    true=eqb_string s s.
Proof.
  intros. unfold eqb_string.
  destruct (string_dec s s) as [| Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem eqb_string_true_iff: forall x y: string,
    eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [| Hs].
  - subst. split.
    reflexivity. reflexivity.
  - split.
    + intros. discriminate H.
    + intros. rewrite H in Hs.
      destruct Hs. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.


(* use function here cause it can generate a lamba
 style value, rather than a definition still need to
 destruct, which means have nothing to do with Type A*)
Definition total_map(A: Type) := string -> A.

Definition t_empty {A: Type}(v: A): total_map A:=
  (fun _ => v).

Definition t_update{A: Type}(m: total_map A)
           (x: string) (v: A):=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition exmplmap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).


Lemma t_apply_empty: forall (A: Type)(x: string)(v: A),
    (_ !-> v) x = v.
Proof.
  intros.
  reflexivity.
Qed.

Lemma t_update_eq: forall (A: Type)(m: total_map A) x v,
    (x !-> v; m) x = v.
Proof.
  intros. unfold t_update.
  unfold eqb_string.
  destruct (string_dec x x) as [| Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
(* FILL IN HERE *) Admitted.


Lemma t_update_shadow: forall (A: Type)(m: total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (eqb_string x x').
  reflexivity. reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y. apply iff_reflect. rewrite <- eqb_string_true_iff.
  reflexivity.
Qed.


Theorem t_update_same : forall(A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (eqb_stringP x x') as [H | H].
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute: forall(A: Type)(m: total_map A)
                           v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1; x2 !-> v2; m)
    =
    (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (eqb_stringP x1 x').
  - destruct (eqb_stringP x2 x').
    + rewrite e in H. rewrite e0 in H.
      destruct H. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Definition partial_map(A: Type) := total_map (option A).

Definition empty{A: Type}: partial_map A :=
  t_empty None.

Definition update{A: Type}(m: partial_map A)
           (x: string)(v: A):=
  (x !-> Some v; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
                         (at level 100).

Example eamaplepmap :=
  ("Church" |-> true; "Turing" |-> false).

Lemma apply_empty : forall (A: Type)(x: string),
    @empty A x= None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity. Qed.


Lemma update_eq : forall(A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall(A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall(A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall(A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall(A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.