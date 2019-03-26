Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even: nat -> Prop :=
| ev_0: even 0
| ev_SS (n: nat) (H: even n) : even(S (S n)).

(* Inductive even : nat -> Prop := *)
(* | ev_0 : even 0 *)
(* | ev_SS : forall n, even n -> even (S (S n)). *)

Theorem ev_double : forall n,
    even (double n).
Proof.
  intros.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS.
    apply IHn.
Qed.

Theorem ev_inversion: forall (n: nat),
    even n ->
    (n=0) \/ (exists n', n=S(S n') /\ even n').
Proof.
  intros n E.
  destruct E as [| n' E'].
  - left. reflexivity.
  - right. exists n'. split.
    reflexivity.
    apply E'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
    even (S(S n)) -> even n.
Proof.
  intros. apply ev_inversion in H.
  destruct H.
  - discriminate.
  - destruct H as [n' [Hnm Hev]].
    injection Hnm. intros Heq.
    rewrite  Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
    even (S (S n)) -> even n.
Proof.
  intros.
  inversion H. apply H1.
Qed.

Theorem even5_nonsence:
  even 5 -> 2+2=9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o: nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros.
  inversion H. reflexivity.
Qed.

Lemma ev_even : forall n,
    even n -> exists k, n=double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' HK'].
    rewrite HK'.
    exists (S k'). simpl. reflexivity.
Qed.


Theorem ev_even_iff : forall n,
    even n <-> exists k, n= double k.
Proof.
  intros. split.
  - apply  ev_even.
  - intros. destruct H.
    rewrite H. apply ev_double.
Qed.

Theorem ev_sum : forall n m,
    even n -> even m -> even (n+m).
Proof.
  intros n m En Em.
  induction En as [| n' En' EnIHn].
  - simpl. apply Em.
  - simpl. apply ev_SS.
    apply  EnIHn.
Qed.

Theorem ev_ev_ev : forall n m,
    even (n+m) -> even n -> even m.
Proof.
  intros n m Enm En.
  induction En as [|n' En' EnIHn].
  - simpl in Enm. apply Enm.
  - inversion Enm.
    apply EnIHn in H0.
    apply H0.
Qed.







