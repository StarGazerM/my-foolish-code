Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Coq Require Import Lists.List.
Import ListNotations.

Module STLCRef.

Inductive ty : Type :=
  | Nat : ty
  | Unit : ty
  | Arrow : ty -> ty -> ty
  | Ref : ty -> ty.

Inductive tm : Type :=
  (* STLC with numbers: *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm
  (* New terms: *)
  | unit : tm
  | ref : tm -> tm
  | deref : tm -> tm
  | assign : tm -> tm -> tm
  | loc : nat -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_nat : forall n,
      value (const n)
  | v_unit :
      value unit
  | v_loc : forall l,
      value (loc l).
Hint Constructors value.

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | abs x' T t1 =>
      if eqb_string x x' then t else abs x' T (subst x s t1)
  | const n =>
      t
  | scc t1 =>
      scc (subst x s t1)
  | prd t1 =>
      prd (subst x s t1)
  | mlt t1 t2 =>
      mlt (subst x s t1) (subst x s t2)
  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      t
  | ref t1 =>
      ref (subst x s t1)
  | deref t1 =>
      deref (subst x s t1)
  | assign t1 t2 =>
      assign (subst x s t1) (subst x s t2)
  | loc _ =>
      t
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


Definition tseq t1 t2 :=
  app (abs "x" Unit t2) t1.

Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st unit.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st =  *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. omega.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st =  *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st =  *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.

Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).
Import ListNotations.
Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T t12 v2 st,
         value v2 ->
         app (abs x T t12) v2 / st --> [x:=v2]t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         app t1 t2 / st --> app t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         app v1 t2 / st --> app v1 t2'/ st'
  | ST_SuccNat : forall n st,
         scc (const n) / st --> const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         scc t1 / st --> scc t1' / st'
  | ST_PredNat : forall n st,
         prd (const n) / st --> const (pred n) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         prd t1 / st --> prd t1' / st'
  | ST_MultNats : forall n1 n2 st,
         mlt (const n1) (const n2) / st --> const (mult n1 n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         mlt t1 t2 / st --> mlt t1' t2 / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         mlt v1 t2 / st --> mlt v1 t2' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         test0 t1 t2 t3 / st --> test0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
         test0 (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         test0 (const (S n)) t2 t3 / st --> t3 / st
  | ST_RefValue : forall v1 st,
         value v1 ->
         ref v1 / st --> loc (length st) / (st ++ v1::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         ref t1 / st --> ref t1' / st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         deref (loc l) / st --> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         deref t1 / st --> deref t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < length st ->
         assign (loc l) v2 / st --> unit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         assign t1 t2 / st --> assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         assign v1 t2 / st --> assign v1 t2' / st'

where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).

Hint Constructors step.
Definition multistep := (multi step).
Notation "t1 '/' st '-->*' t2 '/' st'" :=
               (multistep (t1,st) (t2,st'))
               (at level 40, st at level 39, t2 at level 39).

Definition context := partial_map ty.

Definition store_ty := list ty.

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST Unit.

Reserved Notation "Gamma ';' ST '|-' t '∈' T" (at level 40).
Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall Gamma ST x T,
      Gamma x = Some T ->
      Gamma; ST |- (var x) ∈ T
  | T_Abs : forall Gamma ST x T11 T12 t12,
      (update Gamma x T11); ST |- t12 ∈ T12 ->
      Gamma; ST |- (abs x T11 t12) ∈ (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma ST t1 t2,
      Gamma; ST |- t1 ∈ (Arrow T1 T2) ->
      Gamma; ST |- t2 ∈ T1 ->
      Gamma; ST |- (app t1 t2) ∈ T2
  | T_Nat : forall Gamma ST n,
      Gamma; ST |- (const n) ∈ Nat
  | T_Succ : forall Gamma ST t1,
      Gamma; ST |- t1 ∈ Nat ->
      Gamma; ST |- (scc t1) ∈ Nat
  | T_Pred : forall Gamma ST t1,
      Gamma; ST |- t1 ∈ Nat ->
      Gamma; ST |- (prd t1) ∈ Nat
  | T_Mult : forall Gamma ST t1 t2,
      Gamma; ST |- t1 ∈ Nat ->
      Gamma; ST |- t2 ∈ Nat ->
      Gamma; ST |- (mlt t1 t2) ∈ Nat
  | T_If0 : forall Gamma ST t1 t2 t3 T,
      Gamma; ST |- t1 ∈ Nat ->
      Gamma; ST |- t2 ∈ T ->
      Gamma; ST |- t3 ∈ T ->
      Gamma; ST |- (test0 t1 t2 t3) ∈ T
  | T_Unit : forall Gamma ST,
      Gamma; ST |- unit ∈ Unit
  | T_Loc : forall Gamma ST l,
      l < length ST ->
      Gamma; ST |- (loc l) ∈ (Ref (store_Tlookup l ST))
  | T_Ref : forall Gamma ST t1 T1,
      Gamma; ST |- t1 ∈ T1 ->
      Gamma; ST |- (ref t1) ∈ (Ref T1)
  | T_Deref : forall Gamma ST t1 T11,
      Gamma; ST |- t1 ∈ (Ref T11) ->
      Gamma; ST |- (deref t1) ∈ T11
  | T_Assign : forall Gamma ST t1 t2 T11,
      Gamma; ST |- t1 ∈ (Ref T11) ->
      Gamma; ST |- t2 ∈ T11 ->
      Gamma; ST |- (assign t1 t2) ∈ Unit

where "Gamma ';' ST '|-' t '∈' T" := (has_type Gamma ST t T).
Hint Constructors has_type.

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
        empty; ST |- (store_lookup l st) ∈ (store_Tlookup l ST)).

(* function to extends store because store can be refreshed by other type of store *)
Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).
Hint Constructors extends.

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST ST' Hlen H.
  generalize dependent ST'. generalize dependent l.
  induction ST as [|a ST2]; intros l Hlen ST' HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; omega.
Qed.

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    inversion Hlen.
    simpl in *.
    destruct l; try omega.
      apply lt_n_S. apply IHextends. omega.
Qed.

(* extends store is reflexive *)
Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof with auto.
  induction ST; intros T...
  simpl...
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
  induction ST; auto.
Qed.

Definition preservation_theorem := forall ST t t' T st st',
  empty; ST |- t ∈ T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
    (extends ST' ST /\
     empty; ST' |- t' ∈ T /\
                  store_well_typed ST' st').


Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (abs y T11 t12)
  | afi_succ : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (scc t1)
  | afi_pred : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (prd t1)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (mlt t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (mlt t1 t2)
  | afi_if0_1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test0 t1 t2 t3)
  | afi_if0_3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test0 t1 t2 t3)
  | afi_ref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (ref t1)
  | afi_deref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (deref t1)
  | afi_assign1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (assign t1 t2)
  | afi_assign2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (assign t1 t2).
Hint Constructors appears_free_in.


Lemma free_in_context : forall x t T Gamma ST,
   appears_free_in x t ->
   Gamma; ST |- t ∈ T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros. generalize dependent Gamma. generalize dependent T.
  induction H;
        intros; (try solve [ inversion H0; subst; eauto ]).
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H8.
    rewrite update_neq in H8; assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' ST t T,
  Gamma; ST |- t ∈ T ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma'; ST |- t ∈ T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros...
  - (* T_Var *)
    apply T_Var. symmetry. rewrite <- H...
  - (* T_Abs *)
    apply T_Abs. apply IHhas_type; intros.
    unfold update, t_update.
    destruct (eqb_stringP x x0)...
  - (* T_App *)
    eapply T_App.
      apply IHhas_type1...
      apply IHhas_type2...
  - (* T_Mult *)
    eapply T_Mult.
      apply IHhas_type1...
      apply IHhas_type2...
  - (* T_If0 *)
    eapply T_If0.
      apply IHhas_type1...
      apply IHhas_type2...
      apply IHhas_type3...
  - (* T_Assign *)
    eapply T_Assign.
      apply IHhas_type1...
      apply IHhas_type2...
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x s S t T,
  empty; ST |- s ∈ S ->
  (update Gamma x S); ST |- t ∈ T ->
  Gamma; ST |- ([x:=s]t) ∈ T.
Proof with eauto.
  intros Gamma ST x s S t T Hs Ht.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    inversion H; subst; simpl...
  - (* var *)
    rename s0 into y.
    destruct (eqb_stringP x y).
    + (* x = y *)
      subst.
      rewrite update_eq in H3.
      inversion H3; subst.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ _ _ _ Hcontra Hs)
        as [T' HT'].
      inversion HT'.
    + (* x <> y *)
      apply T_Var.
      rewrite update_neq in H3...
  - (* abs *) subst.
    rename s0 into y.
    destruct (eqb_stringP x y).
    + (* x = y *)
      subst.
      apply T_Abs. eapply context_invariance...
      intros. rewrite update_shadow. reflexivity.
    + (* x <> x0 *)
      apply T_Abs. apply IHt.
      eapply context_invariance...
      intros. unfold update, t_update.
      destruct (eqb_stringP y x0)...
      subst.
      rewrite false_eqb_string...
Qed.


Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty; ST |- t ∈ (store_Tlookup l ST) ->
  store_well_typed ST (replace l t st).
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (l' =? l) eqn: Heqll'.
  - (* l' = l *)
    apply Nat.eqb_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply Nat.eqb_neq in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma; ST |- t ∈ T ->
  Gamma; ST' |- t ∈ T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    erewrite <- extends_lookup...
    apply T_Loc.
    eapply length_extends...
Qed.

Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  empty; ST |- t1 ∈ T1 ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold store_well_typed in *.
  inversion H as [Hlen Hmatch]; clear H.
  rewrite app_length, plus_comm. simpl.
  rewrite app_length, plus_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; inversion Hl as [Hlt | Heq].
    + (* l < length st *)
      apply lt_S_n in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      inversion Heq.
      rewrite app_nth2; try omega.
      rewrite <- Hlen.
      rewrite minus_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. }
        rewrite app_nth2; try omega.
      rewrite minus_diag. simpl. trivial.
Qed.

Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.

Theorem preservation : forall ST t t' T st st',
  empty; ST |- t ∈ T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
    (extends ST' ST /\
     empty; ST' |- t' ∈ T /\
     store_well_typed ST' st').
Proof with eauto using store_weakening, extends_refl.
  remember (@empty ty) as Gamma.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  induction Ht; intros t' HST Hstep;
    subst; try solve_by_invert; inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  (* T_App *)
  - (* ST_AppAbs *) exists ST.
    inversion Ht1; subst.
    split; try split... eapply substitution_preserves_typing...
  - (* ST_App1 *)
    eapply IHHt1 in H0...
    inversion H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_App2 *)
    eapply IHHt2 in H5...
    inversion H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_Succ *)
    + (* ST_Succ *)
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  - (* T_Pred *)
    + (* ST_Pred *)
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  (* T_Mult *)
  - (* ST_Mult1 *)
    eapply IHHt1 in H0...
    inversion H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Mult2 *)
    eapply IHHt2 in H5...
    inversion H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_If0 *)
    + (* ST_If0_1 *)
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'... split...
  (* T_Ref *)
  - (* ST_RefValue *)
    exists (ST ++ T1::nil).
    inversion HST; subst.
    split.
      apply extends_app.
    split.
      replace (Ref T1)
        with (Ref (store_Tlookup (length st) (ST ++ T1::nil))).
      apply T_Loc.
      rewrite <- H. rewrite app_length, plus_comm. simpl. omega.
      unfold store_Tlookup. rewrite <- H. rewrite nth_eq_last.
      reflexivity.
      apply store_well_typed_app; assumption.
  - (* ST_Ref *)
    eapply IHHt in H0...
    inversion H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Deref *)
  - (* ST_DerefLoc *)
    exists ST. split; try split...
    inversion HST as [_ Hsty].
    replace T11 with (store_Tlookup l ST).
    apply Hsty...
    inversion Ht; subst...
  - (* ST_Deref *)
    eapply IHHt in H0...
    inversion H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Assign *)
  - (* ST_Assign *)
    exists ST. split; try split...
    eapply assign_pres_store_typing...
    inversion Ht1; subst...
  - (* ST_Assign1 *)
    eapply IHHt1 in H0...
    inversion H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Assign2 *)
    eapply IHHt2 in H5...
    inversion H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
Qed.
