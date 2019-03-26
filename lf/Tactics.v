Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

(* apply tactics *)

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly_ex :
  (forall n, evenb n=true -> oddb (S n)=true) ->
  oddb 3=true ->
  evenb 4=true.
Proof.
  intros eq1 eq2.
  apply eq2. Qed.


Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H. Qed.

Theorem rev_ex1 : forall(l l': list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  apply rev_involutive. Qed.


Theorem trans_eq : forall(X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.


Theorem S_injective : forall(n m: nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H1.
  assert (H2: n=pred (S n)).
  { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall(n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall(n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  injection H0.
  intros sH1 sH2.
  symmetry. apply sH2.
Qed.

Theorem eqb_0_l : forall n,
    0=?n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - simpl.
    intros H. discriminate H.
Qed.

Example discriminate_ex3:
  forall (X: Type) (x y z:X) (l j: list X),
    x::y::l = [] -> x=z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.


Theorem S_inj : forall(n m: nat)(b: bool),
    (S n)=?(S m) = b ->
    n=?m = b.
Proof.
  intros.
  simpl in H.
  apply H. Qed.

Theorem plus_n_n_injective : forall n m,
    n+n = m+m ->
    n = m.
Proof.
  intros n. induction n as [| n'].
  intros m H. destruct m as [|m'].
    reflexivity.
    inversion H.
  intros m. destruct m as [|m'].
    intros. inversion H.
    intros eq. inversion eq.
    rewrite <- plus_n_Sm in H0. rewrite <- plus_n_Sm in H0.
    inversion H0. apply IHn' in H1. rewrite -> H1. reflexivity.
Qed.
      
Definition square n := n * n.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Lemma mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite plus_assoc.
  reflexivity.
Qed.


Theorem mult_assoc: forall n m p: nat,
    n*(m*p)=(n*m)*p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn. rewrite mult_plus_distr_r.
    reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
  - rewrite plus_comm. reflexivity.
  - rewrite plus_assoc. rewrite H. rewrite plus_assoc. reflexivity.
Qed.


Theorem mult_plus : forall n m : nat, n * S m = n + (n * m).
Proof.
  intros n m.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_swap. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n. induction m as [| m'].
  - rewrite mult_0_r. reflexivity.
  - simpl. rewrite mult_plus. rewrite IHm'. reflexivity.
Qed.

Lemma square_mult: forall n m, square(n*m)=square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert(H: n*m*n=n*n*m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.


