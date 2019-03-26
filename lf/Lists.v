From LF Require Export Induction.
Module NatList.

Inductive natprod: Type :=
        | pair (n1 n2: nat).

Check(pair 3 5).

Definition fst(p: natprod): nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition swap_pair(p: natprod): natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Fixpoint minus(n m:nat): nat :=
  match n,m with
  | O ,_ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.


Theorem snd_fst_is_swap : forall (p: natprod),
    (snd p, fst p)= swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. 
  reflexivity.
Qed.

Inductive natlist: Type :=
| nil
| cons (n:nat) (l: natlist).

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count:nat): natlist :=
  match count with
  | O => nil
  | S count' => n::(repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros(l:natlist): natlist :=
  match l with
  | nil => l
  | h :: t => match h with
             | O => nonzeros t
             | S _ => h :: (nonzeros t)
             end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag): nat :=
  match s with
  | nil => O
  | (x :: xs) => if x =? v then S (count v xs)
                else count v xs
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.


Theorem nil_app : forall l: natlist,
    pred(length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - reflexivity.
  - reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length: forall l: natlist,
    length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite -> app_length.
    rewrite -> plus_comm.
    simpl. rewrite -> IHl'. reflexivity. Qed.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id(x1 x2: id) :=
  match x1, x2 with
    | Id n1, Id n2 => n1 =? n2 
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.
 
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

End NatList.

Inductive id : Type :=
| Id(n: nat).

Definition eqb_id(x1 x2: id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Lemma eqb_nat_refl : forall x: nat,
    true = eqb x x.
Proof.
  intros x.
  induction x as [|x' IHx'].
  - reflexivity.
  - simpl.
    rewrite -> IHx'.
    reflexivity.
Qed.

Theorem eqb_id_refl: forall x: id, true = eqb_id x x.
Proof.
  intros x.
  destruct x.
  simpl. rewrite <- eqb_nat_refl.
  reflexivity.
Qed.


Module PartialMap.
Export NatList.

  Inductive partial_map : Type :=
  | empty
  | record (i: id) (v: nat) (m: partial_map).


  Definition update(d: partial_map)
             (x: id) (value: nat)
    : partial_map :=
    record x value d.

  Fixpoint find(x: id) (d: partial_map): natoption :=
    match d with
    | empty => None
    | record y v d' => if eqb_id x y
                      then Some v
                      else find x d'
    end.

(* some problems here.... *)
(* Theorem update_eq : *)
(*   forall (d : partial_map) (x : id) (v: nat), *)
(*     find x (update d x v) = Some v. *)
(* Proof. *)
(*   intros d x v. *)
(*   simpl. *)
(*   rewrite <- eqb_id_refl. *)
(*   reflexivity. simpl. Qed *)
     
End PartialMap.





