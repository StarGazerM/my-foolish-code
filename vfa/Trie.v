Require Import Coq.Strings.String.
From VFA Require Import Perm.
From VFA Require Import Maps.
Import FunctionalExtensionality.
Module VerySlow.

  Fixpoint loop (input: list nat) (c: nat) (table: total_map bool) : nat :=
    match input with
    | nil => c
    | a::al => if table a
              then loop al (c+1) table
              else loop al c (t_update table a true)
    end.

  Definition collisions (input: list nat) : nat :=
    loop input 0 (t_empty false).
  Example collisions_pi: collisions [3;1;4;1;5;9;2;6] = 1.
  Proof. reflexivity. Qed.

End VerySlow.

Module Integers.

  (*
   binary expression of nat
   1 is xH
   0 + 2n is xO n
   1 + 2n is xI n 
   *)
  Inductive positive: Set :=
  | xI: positive -> positive
  | xO: positive -> positive
  | xH: positive.

  Definition ten := xO (xI (xO xH)).

  Fixpoint positive2nat (p: positive): nat :=
    match p with
    | xI q => 1 + 2 * positive2nat q
    | xO q => 0 + 2 * positive2nat q
    | xH => 1
    end.

  Fixpoint print_in_binary (p: positive) : list nat :=
    match p with
    | xI q => print_in_binary q ++ [1]
    | xO q => print_in_binary q ++ [0]
    | xH => [1]
    end.

  Eval compute in positive2nat ten.

  Notation "p ~ 1" := (xI p)
                        (at level 7, left associativity, format "p '~' '1'").
  Notation "p ~ 0" := (xO p)
                        (at level 7, left associativity, format "p '~' '0'").
  Print ten. (* = xH~0~1~0 : positive *)

  Fixpoint succ x :=
    match x with
    | p ~ 1 => (succ p) ~ 0
    | p ~ 0 => p ~ 1
    | xH => xH ~ 0
    end.

  Fixpoint addc (carry: bool) (x y: positive) {struct x} : positive :=
    match carry, x, y with
    | false, p ~ 1, q ~ 1 => (addc true p q) ~ 0
    | false, p ~ 1, q ~ 0 => (addc false p q) ~ 1
    | false, p ~ 1, xH => (succ p) ~ 0
    | false, p ~ 0, q ~ 1 => (addc false p q) ~ 1
    | false, p ~ 0, q ~ 0 => (addc false p q) ~ 0
    | false, p ~ 0, xH => p ~ 1
    | false, xH, q ~ 1 => (succ q) ~ 0
    | false, xH, q ~ 0 => q ~ 1
    | false, xH, xH => xH ~ 0
    | true, p ~ 1, q ~ 1 => (addc true p q) ~ 1
    | true, p ~ 1, q ~ 0 => (addc true p q) ~ 0
    | true, p ~ 1, xH => (succ p) ~ 1
    | true, p ~ 0, q ~ 1 => (addc true p q) ~ 0
    | true, p ~ 0, q ~ 0 => (addc false p q) ~ 1
    | true, p ~ 0, xH => (succ p) ~ 0
    | true, xH, q ~ 1 => (succ q) ~ 1
    | true, xH, q ~ 0 => (succ q) ~ 0
    | true, xH, xH => xH ~ 1
    end.
  Definition add (x y: positive) : positive := addc false x y.

  Hint Unfold positive2nat.
  Hint Unfold succ.
  Lemma succ_corret: forall p,
      positive2nat (succ p) = S (positive2nat p).
  Proof.
    intros.
    induction p.
    simpl. rewrite IHp. omega.
    auto.
    auto.
  Qed.

  Hint Unfold addc.
  Lemma addc_correct: forall (c: bool) (p q: positive),
      positive2nat (addc c p q) =
      (if c then 1 else 0) + positive2nat p + positive2nat q.
  Proof with auto.
    intros.
    generalize dependent q.
    generalize dependent c.
    induction p;
      destruct c;
      destruct q; simpl;
      try rewrite IHp;
      try rewrite succ_corret; omega.
  Qed.  

  Theorem add_correct : forall (p q:positive),
      positive2nat (add p q) = positive2nat p + positive2nat q.
  Proof.
    intros.
    unfold add.
    apply addc_correct.
  Qed.

  Inductive comparison : Set :=
    Eq : comparison | Lt : comparison | Gt : comparison.

  Fixpoint compare x y {struct x}:=
    match x, y with
    | p ~ 1, q ~ 1 => compare p q
    | p ~ 1, q ~ 0 => match compare p q with Lt => Lt | _ => Gt end
    | p ~ 1, xH => Gt
    | p ~ 0, q ~ 1 => match compare p q with Gt => Gt | _ => Lt end
    | p ~ 0, q ~ 0 => compare p q
    | p ~ 0, xH => Gt
    | xH, q ~ 1 => Lt
    | xH, q ~ 0 => Lt
    | xH, xH => Eq
    end.

  Lemma positive2nat_pos:
    forall p, positive2nat p > 0.
  Proof.
    intros.
    induction p; simpl; omega.
  Qed.

  Theorem compare_correct:
    forall x y,
      match compare x y with
      | Lt => positive2nat x < positive2nat y
      | Eq => positive2nat x = positive2nat y
      | Gt => positive2nat x > positive2nat y
      end.
  Proof with auto.
    induction x; destruct y; simpl;
    try (specialize (IHx y);
         destruct (compare x y); omega)...
    assert (positive2nat x > 0).
    {apply positive2nat_pos. } omega.
    assert (positive2nat x > 0).
    {apply positive2nat_pos. } omega.
    assert (positive2nat y > 0).
    {apply positive2nat_pos. } omega.
    assert (positive2nat y > 0).
    {apply positive2nat_pos. } omega.
  Qed.

Inductive Z : Set :=
  | Z0 : Z
  | Zpos : positive -> Z
  | Zneg : positive -> Z.
    

End Integers.


Print positive.

Module RatherSlow.
Definition total_mapz (A: Type) := Z -> A.
Definition empty {A:Type} (default: A) : total_mapz A := fun _ => default.
Definition update {A:Type} (m : total_mapz A)
                    (x : Z) (v : A) :=
  fun x' => if Z.eqb x x' then v else m x'.
Fixpoint loop (input: list Z) (c: Z) (table: total_mapz bool) : Z :=
  match input with
  | nil => c
  | a::al => if table a
                  then loop al (c+1) table
                  else loop al c (update table a true)
 end.
Definition collisions (input: list Z) := loop input 0 (empty false).
Example collisions_pi: collisions [3;1;4;1;5;9;2;6]%Z = 1%Z.
Proof. reflexivity. Qed.
End RatherSlow.

Inductive trie (A : Type) :=
    | Leaf : trie A
    | Node : trie A -> A -> trie A -> trie A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Definition trie_table (A: Type) : Type := (A * trie A)%type.

Definition empty {A: Type} (default: A) : trie_table A :=
      (default, Leaf).

Fixpoint look {A: Type} (default: A) (i: positive) (m: trie A): A :=
    match m with
    | Leaf => default
    | Node l x r =>
        match i with
        | xH => x
        | xO i' => look default i' l
        | xI i' => look default i' r
        end
    end.
Definition lookup {A: Type} (i: positive) (t: trie_table A) : A :=
   look (fst t) i (snd t).
Fixpoint ins {A: Type} default (i: positive) (a: A) (m: trie A): trie A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf a Leaf
        | xO i' => Node (ins default i' a Leaf) default Leaf
        | xI i' => Node Leaf default (ins default i' a Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l a r
        | xO i' => Node (ins default i' a l) o r
        | xI i' => Node l o (ins default i' a r)
        end
    end.
Definition insert {A: Type} (i: positive) (a: A) (t: trie_table A)
                 : trie_table A :=
  (fst t, ins (fst t) i a (snd t)).
Definition three_ten : trie_table bool :=
 insert 3 true (insert 10 true (empty false)).
Eval compute in three_ten.
(* = (false,
        Node (Node Leaf false (Node (Node Leaf true Leaf) false Leaf))
                 false
                 (Node Leaf true Leaf))
     : trie_table bool  *)
Eval compute in
   map (fun i => lookup i three_ten) [3;1;4;1;5]%positive.
(*      = true; false; false; false; false  : list bool *)


Module FastEnough.
Fixpoint loop (input: list positive) (c: nat) (table: trie_table bool) : nat :=
  match input with
  | nil => c
  | a::al => if lookup a table
                  then loop al (1+c) table
                  else loop al c (insert a true table)
 end.
Definition collisions (input: list positive) := loop input 0 (empty false).
Example collisions_pi: collisions [3;1;4;1;5;9;2;6]%positive = 1.
Proof. reflexivity. Qed.
End FastEnough.

Lemma look_leaf:
  forall A (a:A) j, look a j Leaf = a.
Proof.
  intros. induction j; auto. Qed.

Lemma look_ins_same: forall {A} a k (v:A) t, look a k (ins a k v t) = v.
Proof.
  intros.
  generalize dependent a.
  generalize dependent v.
  generalize dependent t.
  induction k; simpl; destruct t; auto.
Qed.

Lemma neq_pos_1 : forall j k,
    (j ~ 1 <> k ~ 1 -> j <> k)%positive.
Proof.
  intros.
  intros contra.
  subst.
  contradiction. Qed.

Lemma neq_pos_0 : forall j k,
    (j ~ 0 <> k ~ 0 -> j <> k)%positive.
Proof.
  intros.
  intros contra. subst. contradiction. Qed.

Lemma look_ins_other: forall {A} a j k (v:A) t,
    j <> k -> look a j (ins a k v t) = look a j t.
Proof with eauto.
  intros.
  generalize dependent k.
  generalize dependent t.
  induction j; intros; destruct k; destruct t; simpl;
    try apply look_leaf...
  - apply neq_pos_1 in H. rewrite IHj. apply look_leaf. auto.
  - apply neq_pos_1 in H. rewrite IHj...
  - apply neq_pos_0 in H. rewrite IHj. apply look_leaf. auto.
  - apply neq_pos_0 in H. rewrite IHj...
  - contradiction.
  - contradiction.
Qed.

Definition nat2pos (n: nat) : positive := Pos.of_succ_nat n.
Definition pos2nat (n: positive) : nat := pred (Pos.to_nat n).

Lemma pos2nat2pos: forall p, nat2pos (pos2nat p) = p.
Proof. (* You don't need to read this proof! *)
  intro. unfold nat2pos, pos2nat.
  rewrite <- (Pos2Nat.id p) at 2.
  destruct (Pos.to_nat p) eqn:?.
  pose proof (Pos2Nat.is_pos p). omega.
  rewrite <- Pos.of_nat_succ.
  reflexivity.
Qed.

Lemma nat2pos2nat: forall i, pos2nat (nat2pos i) = i.
Proof. (* You don't need to read this proof! *)
  intro. unfold nat2pos, pos2nat.
  rewrite SuccNat2Pos.id_succ.
  reflexivity.
Qed.


Lemma pos2nat_injective: forall p q, pos2nat p = pos2nat q -> p=q.
Proof.
  intros.
  rewrite <- pos2nat2pos.
  rewrite <- H.
  symmetry.
  apply pos2nat2pos. Qed.

Lemma nat2pos_injective: forall i j, nat2pos i = nat2pos j -> i=j.
Proof.
  intros.
  rewrite <- nat2pos2nat. rewrite <- H.
  symmetry. apply nat2pos2nat. Qed.

Fixpoint index_trie {A: Type} (t: trie A) (full: trie_table A) (i: positive) : Prop :=
  match t with
  | Leaf => True
  | Node l x r => (lookup i full = x) /\ (index_trie l full (i ~ 0)) /\ (index_trie r full (i ~ 1))
  end.

Inductive index_trie' {A: Type} : trie A -> trie_table A -> positive -> Prop :=
| ST_Leaf : forall tb i, index_trie' Leaf tb i
| ST_Node : forall l x r tb (i: positive),
    lookup i tb = x ->
    index_trie' l tb (i ~ 0) ->
    index_trie' r tb (i ~ 1) ->
    index_trie' (Node l x r) tb i.
(* | ST_Insert : forall tb i v, *)
(*     index_trie' (snd tb) tb xH -> *)
(*     index_trie' (snd (insert i v tb)) (insert i v tb) xH. *)

Definition is_trie {A: Type} (t: trie_table A) : Prop :=
  index_trie' (snd t) t xH.

Lemma lookup_insert_same : forall {A} i (v:A) t,
    lookup i (insert i v t) = v.
Proof.
  unfold lookup, insert.
  intros. simpl. apply look_ins_same. Qed.


(* Inductive is_trie {A: Type} : trie_table A -> Prop := *)
(* | T_Insert : forall t v i, is_trie t -> is_trie (insert i v t) *)
(* | T_Empty : forall a, is_trie (empty a). *)

Definition abstract {A: Type} (t: trie_table A) (n: nat) : A :=
  lookup (nat2pos n) t.
Definition Abs {A: Type} (t: trie_table A) (m: total_map A) :=
  abstract t = m.

Theorem empty_is_trie: forall {A} (default: A), is_trie (empty default).
Proof.
  intros.
  constructor. Qed.

Theorem insert_is_trie: forall {A} i x (t: trie_table A),
    is_trie t -> is_trie (insert i x t).
Proof.
  unfold is_trie.
  intros.
  simpl. Admitted.


Theorem empty_relate: forall {A} (default: A),
    Abs (empty default) (t_empty default).
Proof.
  unfold Abs. unfold abstract.
  intros.
  apply functional_extensionality.
  intros. unfold lookup. simpl.
  rewrite t_apply_empty. apply look_leaf.
Qed.

Theorem insert_relate: forall {A} k (v: A) t cts,
    is_trie t ->
    Abs t cts ->
    Abs (insert k v t) (t_update cts (pos2nat k) v).
Proof.
  unfold Abs, abstract, lookup, insert, t_update.
  intros.
  rewrite <- H0.
  simpl.
  apply functional_extensionality.
  intros.
  rewrite <- nat2pos2nat with x.
  remember (nat2pos x) as j.
  bdestruct (pos2nat k =? pos2nat j).
  - apply pos2nat_injective in H1.
    subst. rewrite nat2pos2nat. apply look_ins_same.
  - rewrite pos2nat2pos.  rewrite look_ins_other. auto. 
    intros contra. subst. contradiction.
    Qed.


Example Abs_three_ten:
    Abs
       (insert 3 true (insert 10 true (empty false)))
       (t_update (t_update (t_empty false) (pos2nat 10) true) (pos2nat 3) true).
Proof.
try (apply insert_relate; [hnf; auto | ]).
try (apply insert_relate; [hnf; auto | ]).
try (apply empty_relate).
Admitted.

(******************************************************)
(* here is something else *)

Definition iszero (n: nat) : Prop := (n = 0).

Hint Unfold iszero.

Inductive count : (nat -> Prop) -> (list nat) -> nat -> Prop :=
| C_empty: forall f, count f [] 0
| C_Cons1: forall (f: nat -> Prop) x xs n,
    f x ->
    count f xs (n-1) ->
    count f (x :: xs) n
| C_Cons2: forall (f: nat -> Prop) x xs n,
    not (f x) ->
    count f xs n ->
    count f (x :: xs) n.

Example test1:
  count iszero [] 0.
Proof.
  econstructor. Qed.

Example text2:
  count iszero [1;0;0;2;3;0] 3.
Proof.
  apply C_Cons2. unfold iszero. omega.
  apply C_Cons1. unfold iszero. omega.
  apply C_Cons1. unfold iszero. omega.
  apply C_Cons2. unfold iszero. omega.
  apply C_Cons2. unfold iszero. omega.
  apply C_Cons1. unfold iszero. omega.
  apply C_empty. Qed.



 

