Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Check forall n m: nat, n+m=m+n.

Check forall n: nat, n=2.

Check 3=4.

Lemma and_intro: forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - simpl. rewrite <- IHn'.
    reflexivity. Qed.


Example and_exercise:
  forall n m: nat, n+m=0 -> n=0 /\ m=0.
Proof.
  intros.
  destruct n.
  - destruct m.
    split. reflexivity. reflexivity.
    split. reflexivity. discriminate.
  - destruct m.
    split. discriminate. reflexivity.
    split. discriminate. discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q: Prop,
    P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q: Prop,
    P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R: Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP HQR].
  split.
  - split. apply HP.
    apply proj1 in HQR.
    apply HQR.
  - apply proj2 in HQR.
    apply HQR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro: forall A B: Prop, A -> A \/ B.
Proof.
  intros. left. apply H. Qed.

Lemma or_intro2: forall A B: Prop, B -> A \/ B.
Proof.
  intros. right. apply H. Qed.

Lemma zero_or_succ:
  forall n: nat, n = 0 \/ n = S(pred n).
Proof.
  intros [| n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not: forall(P: Prop),
    not P -> (forall (Q: Prop), P -> Q). 
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Notation "x <> y" := (~(x=y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros constra.
  discriminate.
Qed.

Theorem not_false :
  not False.
Proof.
  unfold not.
  intros. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ not P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.


Theorem contrapositive : forall (P Q: Prop),
    (P -> Q) -> (not Q -> not P).
Proof.
  unfold not.
  intros.
  apply H0. apply H. apply H1.
Qed.

Theorem not_both_true_and_false: forall P: Prop, ~(P /\ not P).
Proof.
  unfold not.
  intros P [Left Right].
  apply Right. apply Left.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q: Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split. apply HBA. apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
  
From Coq Require Import Setoids.Setoid.

Lemma four_is_even: exists n: nat, 4=n+n.
Proof.
  exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X: Type)(P:X -> Prop),
    (forall x, P x) -> not(exists x, ~ P x).
Proof.
  unfold not.
  intros.
  destruct H0 as [x E].
  apply E. apply H. Qed.

(* the exists of an element in a list *)
Fixpoint In {A: Type} (x: A) (l: list A): Prop :=
  match l with
  | [] => False
  | x' :: l' => x'=x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff:
  forall (A B: Type)(f: A -> B)(l: list A) (y: B),
    In y (map f l) <->
    exists x, f x=y /\ In x l.
Proof.
  intros. split.
  - induction l.
    + simpl. intros. destruct H.
    + simpl. intros.
      destruct H as [ HFX | HIN].
      exists x. split.
      (* left f x = y case*)
      * apply HFX.
      * apply or_intro. reflexivity.
      (* right (In y map f l)*)
      * apply  IHl in HIN.
        destruct HIN. exists x0.
        split.
        apply proj1 in H. apply H. destruct H.
        right. apply H0.
  - intros. destruct H. destruct H as [ HFX HIN].
    rewrite <- HFX. apply In_map. apply HIN.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.    


Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* apply ... in ... *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for x. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.     

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Axiom function_extensionality: forall {X Y: Type}
                                 {f g: X -> Y},
    (forall (x:X), f x = g x) -> f = g.



Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Print rev.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.


Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

    
Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  Admitted.

Print eqb_eq.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
Admitted.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ not P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

