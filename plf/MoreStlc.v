 Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From Coq Require Import Strings.String.

Module STLCExtended.

  Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
  Tactic Notation "normalize" :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
    apply multi_refl.

  (* Syntax *)
  Inductive ty : Type :=
  | Arrow : ty -> ty -> ty
  | Nat : ty
  | Sum : ty -> ty -> ty
  | List : ty -> ty
  | Unit : ty
  | Prod : ty -> ty -> ty.
  Inductive tm : Type :=
  (* pure STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* numbers *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  | mlt : tm -> tm -> tm
  | test0 : tm -> tm -> tm -> tm
  (* sums *)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> string -> tm -> string -> tm -> tm
  (* i.e., case t0 of inl x1 ⇒ t1 | inr x2 ⇒ t2 *)
  (* lists *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
  (* i.e., lcase t1 of | nil ⇒ t2 | x::y ⇒ t3 *)
  (* unit *)
  | unit : tm
  (* You are going to be working on the following extensions: *)
  (* pairs *)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
  (* let *)
  | tlet : string -> tm -> tm -> tm
         (* i.e., let x = t1 in t2 *)
  (* fix *)
  | tfix : tm -> tm.

  (* substitution *)

  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    (* pure STLC *)
    | var y =>
          if eqb_string x y then s else t
    | abs y T t1 =>
          abs y T (if eqb_string x y then t1 else (subst x s t1))
    | app t1 t2 =>
          app (subst x s t1) (subst x s t2)
    (* numbers *)
    | const n =>
            const n
    | scc t1 =>
          scc (subst x s t1)
    | prd t1 =>
          prd (subst x s t1)
    | mlt t1 t2 =>
          mlt (subst x s t1) (subst x s t2)
    | test0 t1 t2 t3 =>
            test0 (subst x s t1) (subst x s t2) (subst x s t3)
    (* sums *)
    | tinl T t1 =>
           tinl T (subst x s t1)
    | tinr T t1 =>
           tinr T (subst x s t1)
    | tcase t0 y1 t1 y2 t2 =>
            tcase (subst x s t0)
            y1 (if eqb_string x y1 then t1 else (subst x s t1))
            y2 (if eqb_string x y2 then t2 else (subst x s t2))
    (* lists *)
    | tnil T =>
           tnil T
    | tcons t1 t2 =>
            tcons (subst x s t1) (subst x s t2)
    | tlcase t1 t2 y1 y2 t3 =>
             tlcase (subst x s t1) (subst x s t2) y1 y2
             (if eqb_string x y1 then
                t3
              else if eqb_string x y2 then t3
                   else (subst x s t3))
    (* unit *)
    | unit => unit
    (* Complete the following cases. *)
    (* pairs *)
    | pair t1 t2 =>
      pair (subst x s t1) (subst x s t2)
    | fst t1 =>
      fst (subst x s t1)
    | snd t1 =>
      snd (subst x s t1)
    (* let *)
    (* if x = y, nothing need to be changed *)
    | tlet y t1 t2 =>
      tlet y (subst x s t1) (if eqb_string x y then t2 else (subst x s t2))
    (* fix *)
    | tfix t1 =>
      tfix (subst x s t1)
    end.

    Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

    Inductive value : tm -> Prop :=
    (* In pure STLC, function abstractions are values: *)
    | v_abs : forall x T11 t12,
        value (abs x T11 t12)
    (* Numbers are values: *)
    | v_nat : forall n1,
        value (const n1)
    (* A tagged value is a value:  *)
    | v_inl : forall v T,
        value v ->
        value (tinl T v)
    | v_inr : forall v T,
        value v ->
        value (tinr T v)
    (* A list is a value iff its head and tail are values: *)
    | v_lnil : forall T, value (tnil T)
    | v_lcons : forall v1 vl,
        value v1 ->
        value vl ->
        value (tcons v1 vl)
    (* A unit is always a value *)
    | v_unit : value unit
    (* A pair is a value if both components are: *)
    | v_pair : forall v1 v2,
        value v1 ->
        value v2 ->
        value (pair v1 v2).
    Hint Constructors value.
    Reserved Notation "t1 '-->' t2" (at level 40).
    Inductive step : tm -> tm -> Prop :=
    (* pure STLC *)
    | ST_AppAbs : forall x T11 t12 v2,
        value v2 ->
        (app (abs x T11 t12) v2) --> [x:=v2]t12
    | ST_App1 : forall t1 t1' t2,
        t1 --> t1' ->
        (app t1 t2) --> (app t1' t2)
    | ST_App2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        (app v1 t2) --> (app v1 t2')
    (* numbers *)
    | ST_Succ1 : forall t1 t1',
        t1 --> t1' ->
        (scc t1) --> (scc t1')
    | ST_SuccNat : forall n1,
        (scc (const n1)) --> (const (S n1))
    | ST_Pred : forall t1 t1',
        t1 --> t1' ->
        (prd t1) --> (prd t1')
    | ST_PredNat : forall n1,
        (prd (const n1)) --> (const (pred n1))
    | ST_Mult1 : forall t1 t1' t2,
        t1 --> t1' ->
        (mlt t1 t2) --> (mlt t1' t2)
    | ST_Mult2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        (mlt v1 t2) --> (mlt v1 t2')
    | ST_Mulconsts : forall n1 n2,
        (mlt (const n1) (const n2)) --> (const (mult n1 n2))
    | ST_Test01 : forall t1 t1' t2 t3,
        t1 --> t1' ->
        (test0 t1 t2 t3) --> (test0 t1' t2 t3)
    | ST_Test0Zero : forall t2 t3,
        (test0 (const 0) t2 t3) --> t2
    | ST_Test0Nonzero : forall n t2 t3,
        (test0 (const (S n)) t2 t3) --> t3
    (* sums *)
    | ST_Inl : forall t1 t1' T,
        t1 --> t1' ->
        (tinl T t1) --> (tinl T t1')
    | ST_Inr : forall t1 t1' T,
        t1 --> t1' ->
        (tinr T t1) --> (tinr T t1')
    | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        (tcase t0 x1 t1 x2 t2) --> (tcase t0' x1 t1 x2 t2)
    | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinl T v0) x1 t1 x2 t2) --> [x1:=v0]t1
    | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinr T v0) x1 t1 x2 t2) --> [x2:=v0]t2
    (* lists *)
    | ST_Cons1 : forall t1 t1' t2,
        t1 --> t1' ->
        (tcons t1 t2) --> (tcons t1' t2)
    | ST_Cons2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        (tcons v1 t2) --> (tcons v1 t2')
    | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
        t1 --> t1' ->
        (tlcase t1 t2 x1 x2 t3) --> (tlcase t1' t2 x1 x2 t3)
    | ST_LcaseNil : forall T t2 x1 x2 t3,
        (tlcase (tnil T) t2 x1 x2 t3) --> t2
    | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
        value v1 ->
        value vl ->
        (tlcase (tcons v1 vl) t2 x1 x2 t3)
          --> (subst x2 vl (subst x1 v1 t3))

    (* Add rules for the following extensions. *)

    (* pairs *)
    | ST_Pair1 : forall t1 t2 t1',
        t1 --> t1' ->
        (pair t1 t2) --> (pair t1' t2)
    | ST_Pair2 : forall t1 t2 t2',
        t2 --> t2' ->
        (pair t1 t2) --> (pair t1 t2')
    | ST_Fst1 : forall t1 t1',
        t1 --> t1' ->
        (fst t1) --> (fst t1')
    | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (fst (pair v1 v2)) --> v1
    | ST_Snd1 : forall t1 t1',
        t1 --> t1' ->
        (snd t1) --> (snd t1')
    | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (snd (pair v1 v2)) --> v2
    (* let *)
    | ST_Let1 : forall x t1 t1' t2,
        t1 --> t1' ->
        (tlet x t1 t2) --> (tlet x t1' t2)
    |ST_LetValue : forall x v1 t2,
        value v1 ->
        (tlet x v1 t2) --> (subst x v1 t2)
    (* fix *)
    | ST_Fix1 : forall t1 t1',
        t1 --> t1' ->
        (tfix t1) --> (tfix t1')
    | ST_FixAbs : forall xf t2 T1,
        (tfix (abs xf T1 t2)) -->
        (subst xf (tfix (abs xf T1 t2)) t2)

    where "t1 '-->' t2" := (step t1 t2).
    Notation multistep := (multi step).
    Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
    Hint Constructors step.

    Definition context := partial_map ty.

    Reserved Notation "Gamma '|-' t '∈' T" (at level 40).
    Inductive has_type : context -> tm -> ty -> Prop :=
    (* Typing rules for pure STLC *)
    | T_Var : forall Gamma x T,
        Gamma x = Some T ->
        Gamma |- (var x) ∈ T
    | T_Abs : forall Gamma x T11 T12 t12,
        (update Gamma x T11) |- t12 ∈ T12 ->
        Gamma |- (abs x T11 t12) ∈ (Arrow T11 T12)
    | T_App : forall T1 T2 Gamma t1 t2,
        Gamma |- t1 ∈ (Arrow T1 T2) ->
        Gamma |- t2 ∈ T1 ->
        Gamma |- (app t1 t2) ∈ T2
    (* numbers *)
    | T_Nat : forall Gamma n1,
        Gamma |- (const n1) ∈ Nat
    | T_Succ : forall Gamma t1,
        Gamma |- t1 ∈ Nat ->
        Gamma |- (scc t1) ∈ Nat
    | T_Pred : forall Gamma t1,
        Gamma |- t1 ∈ Nat ->
        Gamma |- (prd t1) ∈ Nat
    | T_Mult : forall Gamma t1 t2,
        Gamma |- t1 ∈ Nat ->
        Gamma |- t2 ∈ Nat ->
        Gamma |- (mlt t1 t2) ∈ Nat
    | T_Test0 : forall Gamma t1 t2 t3 T1,
        Gamma |- t1 ∈ Nat ->
        Gamma |- t2 ∈ T1 ->
        Gamma |- t3 ∈ T1 ->
        Gamma |- (test0 t1 t2 t3) ∈ T1
    (* sums *)
    | T_Inl : forall Gamma t1 T1 T2,
        Gamma |- t1 ∈ T1 ->
        Gamma |- (tinl T2 t1) ∈ (Sum T1 T2)
    | T_Inr : forall Gamma t2 T1 T2,
        Gamma |- t2 ∈ T2 ->
        Gamma |- (tinr T1 t2) ∈ (Sum T1 T2)
    | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
        Gamma |- t0 ∈ (Sum T1 T2) ->
        (update Gamma x1 T1) |- t1 ∈ T ->
        (update Gamma x2 T2) |- t2 ∈ T ->
        Gamma |- (tcase t0 x1 t1 x2 t2) ∈ T
    (* lists *)
    | T_Nil : forall Gamma T,
        Gamma |- (tnil T) ∈ (List T)
    | T_Cons : forall Gamma t1 t2 T1,
        Gamma |- t1 ∈ T1 ->
        Gamma |- t2 ∈ (List T1) ->
        Gamma |- (tcons t1 t2) ∈ (List T1)
    | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
        Gamma |- t1 ∈ (List T1) ->
        Gamma |- t2 ∈ T2 ->
        (update (update Gamma x2 (List T1)) x1 T1) |- t3 ∈ T2 ->
        Gamma |- (tlcase t1 t2 x1 x2 t3) ∈ T2
    (* unit *)
    | T_Unit : forall Gamma,
        Gamma |- unit ∈ Unit

    (* Add rules for the following extensions. *)

    (* pairs *)
    | T_Pair : forall Gamma t1 t2 T1 T2,
        Gamma |- t1 ∈ T1 ->
        Gamma |- t2 ∈ T2 ->
        Gamma |- (pair t1 t2) ∈ (Prod T1 T2)
    | T_Fst : forall Gamma t T1 T2,
        Gamma |- t ∈ (Prod T1 T2) ->
        Gamma |- (fst t) ∈ T1
    | T_Snd : forall Gamma t T1 T2,
        Gamma |- t ∈ (Prod T1 T2) ->
        Gamma |- (snd t) ∈ T2
    (* let *)
    | T_Let : forall Gamma x t1 t2 T1 T2,
        Gamma |- t1 ∈ T1 ->
        (x |-> T1; Gamma) |- t2 ∈ T2 ->
        Gamma |- (tlet x t1 t2) ∈ T2
    (* fix *)
    | T_Fix : forall Gamma t1 T1,
        Gamma |- t1 ∈ (Arrow T1 T1) ->
        Gamma |- (tfix t1) ∈ T1

    where "Gamma '|-' t '∈' T" := (has_type Gamma t T).
    Hint Constructors has_type.

    Module Examples.

      Open Scope string_scope.
      Notation x := "x".
      Notation y := "y".
      Notation a := "a".
      Notation f := "f".
      Notation g := "g".
      Notation l := "l".
      Notation k := "k".
      Notation i1 := "i1".
      Notation i2 := "i2".
      Notation processSum := "processSum".
      Notation n := "n".
      Notation eq := "eq".
      Notation m := "m".
      Notation evenodd := "evenodd".
      Notation even := "even".
      Notation odd := "odd".
      Notation eo := "eo".

      Hint Extern 2 (has_type _ (app _ _) _) =>
           eapply T_App; auto.
      Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
           eapply T_Lcase; auto.
      Hint Extern 2 (_ = _) => compute; reflexivity.

      Module Numtest.
        (* test0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
        Definition test :=
          test0
            (prd
               (scc
                  (prd
                     (mlt
                        (const 2)
                        (const 0)))))
            (const 5)
            (const 6).
        Example typechecks :
          empty |- test ∈ Nat.
        Proof.
          unfold test.
          (* This typing derivation is quite deep, so we need
     to increase the max search depth of auto from the
     default 5 to 10. *)
          auto 10.
        Qed.

        Example numtest_reduces :
          test -->* const 5.
        Proof.
          unfold test.
          normalize.
        Qed.

        (* 
  unfold test. normalize.
         *)
      End Numtest.

      Module Prodtest.
        (* ((5,6),7).fst.snd *)
        Definition test :=
          snd
            (fst
               (pair
                  (pair
                     (const 5)
                     (const 6))
                  (const 7))).
        Example typechecks :
          empty |- test ∈ Nat.
        Proof. unfold test. eauto 15.
               Qed.
        (* GRADE_THEOREM 0.25: typechecks *)
        Example reduces :
          test -->* const 6.
        Proof. 
          unfold test. normalize.
          (* FILL IN HERE *)
        Qed.

        (* GRADE_THEOREM 0.25: reduces *)
      End Prodtest.

      Module LetTest.
        (* let x = pred 6 in succ x *)
        Definition test :=
          tlet
            x
            (prd (const 6))
            (scc (var x)).
        Example typechecks :
          empty |- test ∈ Nat.
        Proof.
          unfold test. eauto 15.
        Qed.
        (* GRADE_THEOREM 0.25: typechecks *)
        Example reduces :
          test -->* const 6.
        Proof.
          unfold test. normalize.
        Qed.

        (* GRADE_THEOREM 0.25: reduces *)
      End LetTest.

      Module Sumtest1.
        (* case (inl Nat 5) of
     inl x => x
   | inr y => y *)
        Definition test :=
          tcase (tinl Nat (const 5))
                x (var x)
                y (var y).
        Example typechecks :
          empty |- test ∈ Nat.
        Proof. unfold test. eauto 15. Qed.
        Example reduces :
          test -->* (const 5).
        Proof.
          unfold test. normalize. Qed.
      End Sumtest1.
      Module Sumtest2.
        (* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)
        Definition test :=
          tlet
            processSum
            (abs x (Sum Nat Nat)
                 (tcase (var x)
                        n (var n)
                        n (test0 (var n) (const 1) (const 0))))
            (pair
               (app (var processSum) (tinl Nat (const 5)))
               (app (var processSum) (tinr Nat (const 5)))).
        Example typechecks :
          empty |- test ∈ (Prod Nat Nat).
        Proof. unfold test. eauto 15. Qed.
        Example reduces :
          test -->* (pair (const 5) (const 0)).
        Proof.
          unfold test. normalize. Qed.
         
      End Sumtest2.
      
      Module ListTest.
        (* let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of
     nil => 0
   | x::y => x*x *)
        Definition test :=
          tlet l
               (tcons (const 5) (tcons (const 6) (tnil Nat)))
               (tlcase (var l)
                       (const 0)
                       x y (mlt (var x) (var x))).
        Example typechecks :
          empty |- test ∈ Nat.
        Proof. unfold test. eauto 20. Qed.
        Example reduces :
          test -->* (const 25).
        Proof.
          unfold test. normalize. Qed.
      End ListTest.

        Module FixTest1.
      (* fact := fix
             (\f:nat->nat.
                \a:nat.
                   test a=0 then 1 else a * (f (pred a))) *)
          Definition fact :=
            tfix
              (abs f (Arrow Nat Nat)
                   (abs a Nat
                        (test0
                           (var a)
                           (const 1)
                           (mlt
                              (var a)
                              (app (var f) (prd (var a))))))).

          Example typechecks :
            empty |- fact ∈ (Arrow Nat Nat).
          Proof. unfold fact. auto 10. Qed. (* FILL IN HERE *)
          (* GRADE_THEOREM 0.25: typechecks *)
          Example reduces :
            (app fact (const 4)) -->* (const 24).
          Proof.
          (* 
  unfold fact. normalize.
           *)
          (* FILL IN HERE *) Admitted.
          (* GRADE_THEOREM 0.25: reduces *)
    End FixTest1.
    Module FixTest2.
      (* map :=
     \g:nat->nat.
       fix
         (\f:nat->nat.
            \l:nat.
               case l of
               |  -> 
               | x::l -> (g x)::(f l)) *)
      Definition map :=
        abs g (Arrow Nat Nat)
            (tfix
               (abs f (Arrow (List Nat) (List Nat))
                    (abs l (List Nat)
                         (tlcase (var l)
                                 (tnil Nat)
                                 a l (tcons (app (var g) (var a))
                                            (app (var f) (var l))))))).
      Example typechecks :
        empty |- map ∈
              (Arrow (Arrow Nat Nat)
                     (Arrow (List Nat)
                            (List Nat))).
      Proof. unfold map. auto 10. Qed.
      (* GRADE_THEOREM 0.25: typechecks *)
      Example reduces :
        app (app map (abs a Nat (scc (var a))))
            (tcons (const 1) (tcons (const 2) (tnil Nat)))
            -->* (tcons (const 2) (tcons (const 3) (tnil Nat))).
      Proof.
        unfold map. normalize. Qed.

      (* GRADE_THEOREM 0.25: reduces *)
    End FixTest2.
    Module FixTest3.
      (* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             test0 m then (test0 n then 1 else 0)
             else test0 n then 0
             else eq (pred m) (pred n))   *)
      Definition equal :=
        tfix
          (abs eq (Arrow Nat (Arrow Nat Nat))
               (abs m Nat
                    (abs n Nat
                         (test0 (var m)
                                (test0 (var n) (const 1) (const 0))
                                (test0 (var n)
                                       (const 0)
                                       (app (app (var eq)
                                                 (prd (var m)))
                                            (prd (var n)))))))).
      Example typechecks :
        empty |- equal ∈ (Arrow Nat (Arrow Nat Nat)).
      Proof. unfold equal. auto 10. Qed.
      (* GRADE_THEOREM 0.25: typechecks *)
      Example reduces :
        (app (app equal (const 4)) (const 4)) -->* (const 1).
      Proof.      
        unfold equal. normalize. Qed.
       
      (* GRADE_THEOREM 0.25: reduces *)
      Example reduces2 :
        (app (app equal (const 4)) (const 5)) -->* (const 0).
      Proof.
        unfold equal. normalize. Qed.
    End FixTest3.
    Module FixTest4.
      (* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. test0 n then 1 else eo.snd (pred n) in
              let o = \n:Nat. test0 n then 0 else eo.fst (pred n) in
              (e,o)) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)
       *)
      Definition eotest :=
        tlet evenodd
             (tfix
                (abs eo (Prod (Arrow Nat Nat) (Arrow Nat Nat))
                     (pair
                        (abs n Nat
                             (test0 (var n)
                                    (const 1)
                                    (app (snd (var eo)) (prd (var n)))))
                        (abs n Nat
                             (test0 (var n)
                                    (const 0)
                                    (app (fst (var eo)) (prd (var n))))))))
             (tlet even (fst (var evenodd))
                   (tlet odd (snd (var evenodd))
                         (pair
                            (app (var even) (const 3))
                            (app (var even) (const 4))))).
      Example typechecks :
        empty |- eotest ∈ (Prod Nat Nat).
      Proof. unfold eotest. eauto 30. Qed.
      (* GRADE_THEOREM 0.25: typechecks *)
      Example reduces :
        eotest -->* (pair (const 0) (const 1)).
      Proof.
        unfold eotest. normalize. Qed.
      (* GRADE_THEOREM 0.25: reduces *)
    End FixTest4.
    End Examples.

    Theorem progress : forall t T,
        empty |- t ∈ T ->
        value t \/ exists t', t --> t'.
    Proof with eauto.
      intros t T Ht.
      remember empty as Gamma.
      generalize dependent HeqGamma.
      induction Ht; intros HeqGamma; subst.
      - (* T_Var *)
        (* The final rule in the given typing derivation cannot be
       T_Var, since it can never be the case that
       empty ⊢ x : T (since the context is empty). *)
        inversion H.
      - (* T_Abs *)
        (* If the T_Abs rule was the last used, then
       t = abs x T11 t12, which is a value. *)
        left...
      - (* T_App *)
        (* If the last rule applied was T_App, then t = t1 t2,
       and we know from the form of the rule that
         empty ⊢ t1 : T1 → T2
         empty ⊢ t2 : T1
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
        right.
        destruct IHHt1; subst...
        + (* t1 is a value *)
          destruct IHHt2; subst...
          * (* t2 is a value *)
            (* If both t1 and t2 are values, then we know that
           t1 = abs x T11 t12, since abstractions are the
           only values that can have an arrow type.  But
           (abs x T11 t12) t2 --> [x:=t2]t12 by ST_AppAbs. *)
            inversion H; subst; try solve_by_invert.
            exists(subst x t2 t12)...
          * (* t2 steps *)
            (* If t1 is a value and t2 --> t2',
           then t1 t2 --> t1 t2' by ST_App2. *)
            inversion H0 as [t2' Hstp]. exists (app t1 t2')...
        + (* t1 steps *)
          (* Finally, If t1 --> t1', then t1 t2 --> t1' t2
         by ST_App1. *)
          inversion H as [t1' Hstp]. exists (app t1' t2)...
      - (* T_Nat *)
        left...
      - (* T_Succ *)
        right.
        destruct IHHt...
        + (* t1 is a value *)
          inversion H; subst; try solve_by_invert.
          exists (const (S n1))...
        + (* t1 steps *)
          inversion H as [t1' Hstp].
          exists (scc t1')...
      - (* T_Pred *)
        right.
        destruct IHHt...
        + (* t1 is a value *)
          inversion H; subst; try solve_by_invert.
          exists(const (pred n1))...
        + (* t1 steps *)
          inversion H as [t1' Hstp].
          exists(prd t1')...
      - (* T_Mult *)
        right.
        destruct IHHt1...
        + (* t1 is a value *)
          destruct IHHt2...
          * (* t2 is a value *)
            inversion H; subst; try solve_by_invert.
            inversion H0; subst; try solve_by_invert.
            exists(const (mult n1 n0))...
          * (* t2 steps *)
            inversion H0 as [t2' Hstp].
            exists(mlt t1 t2')...
        + (* t1 steps *)
          inversion H as [t1' Hstp].
          exists(mlt t1' t2)...
      - (* T_Test0 *)
        right.
        destruct IHHt1...
        + (* t1 is a value *)
          inversion H; subst; try solve_by_invert.
          destruct n1 as [|n1'].
          * (* n1=0 *)
            exists t2...
          * (* n1<>0 *)
            exists t3...
        + (* t1 steps *)
          inversion H as [t1' H0].
          exists (test0 t1' t2 t3)...
      - (* T_Inl *)
        destruct IHHt...
        + (* t1 steps *)
          right. inversion H as [t1' Hstp]...
      (* exists (tinl _ t1')... *)
      - (* T_Inr *)
        destruct IHHt...
        + (* t1 steps *)
          right. inversion H as [t1' Hstp]...
      (* exists (tinr _ t1')... *)
      - (* T_Case *)
        right.
        destruct IHHt1...
        + (* t0 is a value *)
          inversion H; subst; try solve_by_invert.
          * (* t0 is inl *)
            exists ([x1:=v]t1)...
          * (* t0 is inr *)
            exists ([x2:=v]t2)...
        + (* t0 steps *)
          inversion H as [t0' Hstp].
          exists (tcase t0' x1 t1 x2 t2)...
      - (* T_Nil *)
        left...
      - (* T_Cons *)
        destruct IHHt1...
        + (* head is a value *)
          destruct IHHt2...
          * (* tail steps *)
            right. inversion H0 as [t2' Hstp].
            exists (tcons t1 t2')...
        + (* head steps *)
          right. inversion H as [t1' Hstp].
          exists (tcons t1' t2)...
      - (* T_Lcase *)
        right.
        destruct IHHt1...
        + (* t1 is a value *)
          inversion H; subst; try solve_by_invert.
          * (* t1=tnil *)
            exists t2...
          * (* t1=tcons v1 vl *)
            exists ([x2:=vl]([x1:=v1]t3))...
        + (* t1 steps *)
          inversion H as [t1' Hstp].
          exists (tlcase t1' t2 x1 x2 t3)...
      - (* T_Unit *)
        left...
      - (* pairs *)
        destruct IHHt1...
        + (* t1 is value *)
          destruct IHHt2...
          inversion H0. eauto.
        + (* t1 steps *)
          destruct IHHt2...
          inversion H. eauto.
          destruct H. destruct H0. eauto.
      - (* fst *)
        destruct IHHt...
        right. inversion Ht;subst; try solve_by_invert.
        inversion H;subst. eauto.
        right. destruct H. eauto.
      - destruct IHHt...
        right. inversion Ht; subst;try solve_by_invert.
        inversion H...
        right. destruct H...
      - (* let *)
        right.
        destruct IHHt1...
        destruct H...
      - (* fix *)
        right.
        destruct IHHt...
        inversion H;subst; try solve_by_invert.
        eauto.
        destruct H...
    Qed.

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
    (* numbers *)
    | afi_succ : forall x t,
        appears_free_in x t ->
        appears_free_in x (scc t)
    | afi_pred : forall x t,
        appears_free_in x t ->
        appears_free_in x (prd t)
    | afi_mult1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (mlt t1 t2)
    | afi_mult2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (mlt t1 t2)
    | afi_test01 : forall x t1 t2 t3,
        appears_free_in x t1 ->
        appears_free_in x (test0 t1 t2 t3)
    | afi_test02 : forall x t1 t2 t3,
        appears_free_in x t2 ->
        appears_free_in x (test0 t1 t2 t3)
    | afi_test03 : forall x t1 t2 t3,
        appears_free_in x t3 ->
        appears_free_in x (test0 t1 t2 t3)
    (* sums *)
    | afi_inl : forall x t T,
        appears_free_in x t ->
        appears_free_in x (tinl T t)
    | afi_inr : forall x t T,
        appears_free_in x t ->
        appears_free_in x (tinr T t)
    | afi_case0 : forall x t0 x1 t1 x2 t2,
        appears_free_in x t0 ->
        appears_free_in x (tcase t0 x1 t1 x2 t2)
    | afi_case1 : forall x t0 x1 t1 x2 t2,
        x1 <> x ->
        appears_free_in x t1 ->
        appears_free_in x (tcase t0 x1 t1 x2 t2)
    | afi_case2 : forall x t0 x1 t1 x2 t2,
        x2 <> x ->
        appears_free_in x t2 ->
        appears_free_in x (tcase t0 x1 t1 x2 t2)
    (* lists *)
    | afi_cons1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (tcons t1 t2)
    | afi_cons2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (tcons t1 t2)
    | afi_lcase1 : forall x t1 t2 y1 y2 t3,
        appears_free_in x t1 ->
        appears_free_in x (tlcase t1 t2 y1 y2 t3)
    | afi_lcase2 : forall x t1 t2 y1 y2 t3,
        appears_free_in x t2 ->
        appears_free_in x (tlcase t1 t2 y1 y2 t3)
    | afi_lcase3 : forall x t1 t2 y1 y2 t3,
        y1 <> x ->
        y2 <> x ->
        appears_free_in x t3 ->
        appears_free_in x (tlcase t1 t2 y1 y2 t3)

    (* Add rules for the following extensions. *)

    (* pairs *)
    | afi_pair1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (pair t1 t2)
    | afi_pair2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (pair t1 t2)
    | afi_fst : forall x t,
        appears_free_in x t ->
        appears_free_in x (fst t)
    | afi_snd : forall x t,
        appears_free_in x t ->
        appears_free_in x (snd t)
    (* let *)
    (* y is not in t1 here no no need to check eq of x y *)
    | afi_let1 : forall x y t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (tlet y t1 t2)
    | afi_let2 : forall x y t1 t2,
        x <> y ->
        appears_free_in x t2 ->
        appears_free_in x (tlet y t1 t2)
    (* fix *)
    | afi_fix : forall x t,
        appears_free_in x t ->
        appears_free_in x (tfix t)
    .
    Hint Constructors appears_free_in.

    Lemma context_invariance : forall Gamma Gamma' t S,
        Gamma |- t ∈ S ->
        (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
        Gamma' |- t ∈ S.
    (* Increasing the depth of eauto allows some more simple cases to
   be dispatched automatically. *)
    Proof with eauto 30.
      intros. generalize dependent Gamma'.
      induction H;
        intros Gamma' Heqv...
      - (* T_Var *)
        apply T_Var... rewrite <- Heqv...
      - (* T_Abs *)
        apply T_Abs... apply IHhas_type. intros y Hafi.
        unfold update, t_update.
        destruct (eqb_stringP x y)...
      - (* T_Case *)
        eapply T_Case...
        + apply IHhas_type2. intros y Hafi.
          unfold update, t_update.
          destruct (eqb_stringP x1 y)...
        + apply IHhas_type3. intros y Hafi.
          unfold update, t_update.
          destruct (eqb_stringP x2 y)...
      - (* T_Lcase *)
        eapply T_Lcase... apply IHhas_type3. intros y Hafi.
        unfold update, t_update.
        destruct (eqb_stringP x1 y)...
        destruct (eqb_stringP x2 y)...
      - (* T_Let *)
        econstructor.
        eapply IHhas_type1. intros. apply Heqv.
        econstructor...
        eapply IHhas_type2. intros.
        unfold update, t_update.
        destruct (eqb_stringP x x0)...
    Qed.

    Lemma free_in_context : forall x t T Gamma,
        appears_free_in x t ->
        Gamma |- t ∈ T ->
        exists T', Gamma x = Some T'.
    Proof with eauto.
      intros x t T Gamma Hafi Htyp.
      induction Htyp; inversion Hafi; subst...
      - (* T_Abs *)
        destruct IHHtyp as [T' Hctx]... exists T'.
        unfold update, t_update in Hctx.
        rewrite false_eqb_string in Hctx...
      (* T_Case *)
      - (* left *)
        destruct IHHtyp2 as [T' Hctx]... exists T'.
        unfold update, t_update in Hctx.
        rewrite false_eqb_string in Hctx...
      - (* right *)
        destruct IHHtyp3 as [T' Hctx]... exists T'.
        unfold update, t_update in Hctx.
        rewrite false_eqb_string in Hctx...
      - (* T_Lcase *)
        clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
        destruct IHHtyp3 as [T' Hctx]... exists T'.
        unfold update, t_update in Hctx.
        rewrite false_eqb_string in Hctx...
        rewrite false_eqb_string in Hctx...
      - (* T_Let *)
        apply IHHtyp2 in H4. destruct H4. exists x1.
        unfold update, t_update in H.
        rewrite false_eqb_string in H...
    Qed.

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
        (update Gamma x U) |- t ∈ S ->
        empty |- v ∈ U ->
        Gamma |- ([x:=v]t) ∈ S.
    Proof with eauto.
      (* Theorem: If (x⊢>U ; Gamma) ⊢ t ∈ S and empty ⊢ v ∈ U,
     then Gamma ⊢ [x:=v]t ∈ S. *)
      intros Gamma x U v t S Htypt Htypv.
      generalize dependent Gamma. generalize dependent S.
      (* Proof: By induction on the term t.  Most cases follow
     directly from the IH, with the exception of var
     and abs. These aren't automatic because we must
     reason about how the variables interact. *)
      induction t;
        intros S Gamma Htypt; simpl; inversion Htypt; subst...
      - (* var *)
        simpl. rename s into y.
        (* If t = y, we know that empty ⊢ v ∈ U
                            and (x⊢>U;Gamma) ⊢ y ∈ S
       and, by inversion, update Gamma x U y = Some S.
       We want to show that Gamma ⊢ [x:=v]y ∈ S.

       There are two cases to consider: either x=y or x≠y. *)
        unfold update, t_update in H1.
        destruct (eqb_stringP x y).
        + (* x=y *)
          (* If x = y, then we know that U = S, and that
         [x:=v]y = v.  So what we really must show is
         that if empty ⊢ v ∈ U then Gamma ⊢ v ∈ U.
         We have already proven a more general version
         of this theorem, called context invariance. *)
          subst.
          inversion H1; subst. clear H1.
          eapply context_invariance...
          intros x Hcontra.
          destruct (free_in_context _ _ S empty Hcontra)
            as [T' HT']...
          inversion HT'.
        + (* x<>y *)
          (* If x ≠ y, then Gamma y = Some S and the substitution has no
       effect.  We can show that Gamma ⊢ y ∈ S by T_Var. *)
          apply T_Var...
      - (* abs *)
        rename s into y. rename t into T11.
        (* If t = abs y T11 t0, then we know that
         (x⊢>U;Gamma) ⊢ abs y T11 t0 ∈ T11→T12
         (y⊢>T11;x⊢>U;Gamma) ⊢ t0 ∈ T12
         empty ⊢ v ∈ U
       As our IH, we know that for all S and Gamma,
         if (x⊢>U;Gamma) ⊢ t0 ∈ S
         then Gamma ⊢ [x:=v]t0 ∈ S.

       We can calculate that
         [x:=v]t = abs y T11 (if eqb_string x y then t0 else [x:=v]t0)
       And we must show that Gamma ⊢ [x:=v]t ∈ T11→T12.  We know
       we will do so using T_Abs, so it remains to be shown that:
         (y⊢>T11;Gamma) ⊢ if eqb_string x y then t0 else [x:=v]t0 ∈ T12
       We consider two cases: x = y and x ≠ y.
         *)
        apply T_Abs...
        destruct (eqb_stringP x y) as [Hxy|Hxy].
        + (* x=y *)
          (* If x = y, then the substitution has no effect.  Context
       invariance shows that y:T11;y⊢>U;Gamma and y⊢>T11;Gamma
       are equivalent.  Since the former context shows that
       t0 ∈ T12, so does the latter. *)
          eapply context_invariance...
          subst.
          intros x Hafi. unfold update, t_update.
          destruct (eqb_string y x)...
        + (* x<>y *)
          (* If x ≠ y, then the IH and context invariance allow
         us to show that
           (y⊢>T11;x⊢>U;Gamma) ⊢ t0 ∈ T12       =>
           (x⊢>U;y⊢>T11;Gamma) ⊢ t0 ∈ T12       =>
           (y⊢>T11;Gamma) ⊢ [x:=v]t0 ∈ T12 *)
          apply IHt. eapply context_invariance...
          intros z Hafi. unfold update, t_update.
          destruct (eqb_stringP y z) as [Hyz|Hyz]...
          subst.
          rewrite false_eqb_string...
      - (* tcase *)
        rename s into x1. rename s0 into x2.
        eapply T_Case...
        + (* left arm *)
          destruct (eqb_stringP x x1) as [Hxx1|Hxx1].
          * (* x = x1 *)
            eapply context_invariance...
            subst.
            intros z Hafi. unfold update, t_update.
            destruct (eqb_string x1 z)...
          * (* x <> x1 *)
            apply IHt2. eapply context_invariance...
            intros z Hafi. unfold update, t_update.
            destruct (eqb_stringP x1 z) as [Hx1z|Hx1z]...
            subst. rewrite false_eqb_string...
        + (* right arm *)
          destruct (eqb_stringP x x2) as [Hxx2|Hxx2].
          * (* x = x2 *)
            eapply context_invariance...
            subst.
            intros z Hafi. unfold update, t_update.
            destruct (eqb_string x2 z)...
          * (* x <> x2 *)
            apply IHt3. eapply context_invariance...
            intros z Hafi. unfold update, t_update.
            destruct (eqb_stringP x2 z)...
            subst. rewrite false_eqb_string...
      - (* tlcase *)
        rename s into y1. rename s0 into y2.
        eapply T_Lcase...
        destruct (eqb_stringP x y1).
        + (* x=y1 *)
          simpl.
          eapply context_invariance...
          subst.
          intros z Hafi. unfold update, t_update.
          destruct (eqb_stringP y1 z)...
        + (* x<>y1 *)
          destruct (eqb_stringP x y2).
          * (* x=y2 *)
            eapply context_invariance...
            subst.
            intros z Hafi. unfold update, t_update.
            destruct (eqb_stringP y2 z)...
          * (* x<>y2 *)
            apply IHt3. eapply context_invariance...
            intros z Hafi. unfold update, t_update.
            destruct (eqb_stringP y1 z)...
            subst. rewrite false_eqb_string...
            destruct (eqb_stringP y2 z)...
            subst. rewrite false_eqb_string...
      - (* tlet *)
        econstructor...
        destruct (eqb_stringP x s).
        + subst.
          rewrite update_shadow in H5...
        + apply IHt2.
          rewrite update_permute...
    Qed.


    Theorem preservation : forall t t' T,
        empty |- t ∈ T ->
        t --> t' ->
        empty |- t' ∈ T.
    Proof with eauto.
      intros t t' T HT.
      (* Theorem: If empty ⊢ t ∈ T and t --> t', then
     empty ⊢ t' ∈ T. *)
      remember empty as Gamma. generalize dependent HeqGamma.
      generalize dependent t'.
      (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory (T_Var, T_Abs).  We show just
     the interesting ones. *)
      induction HT;
        intros t' HeqGamma HE; subst; inversion HE; subst...
      - (* T_App *)
        (* If the last rule used was T_App, then t = t1 t2, and
       three rules could have been used to show t --> t':
       ST_App1, ST_App2, and ST_AppAbs. In the first two
       cases, the result follows directly from the IH. *)
        inversion HE; subst...
        + (* ST_AppAbs *)
          (* For the third case, suppose
           t1 = abs x T11 t12
         and
           t2 = v2.
         We must show that empty ⊢ [x:=v2]t12 ∈ T2.
         We know by assumption that
             empty ⊢ abs x T11 t12 ∈ T1→T2
         and by inversion
             x⊢>T1 ⊢ t12 ∈ T2
         We have already proven that substitution preserves
         typing, and
             empty ⊢ v2 ∈ T1
         by assumption, so we are done. *)
          apply substitution_preserves_typing with T1...
          inversion HT1...
      (* T_Case *)
      - (* ST_CaseInl *)
        inversion HT1; subst.
        eapply substitution_preserves_typing...
      - (* ST_CaseInr *)
        inversion HT1; subst.
        eapply substitution_preserves_typing...
      - (* T_Lcase *)
        + (* ST_LcaseCons *)
          inversion HT1; subst.
          apply substitution_preserves_typing with (List T1)...
          apply substitution_preserves_typing with T1...
      - inversion HT;subst...
      - inversion HT;subst...
      - eapply substitution_preserves_typing...
      - eapply substitution_preserves_typing...
        inversion HT;subst...
    Qed.


End STLCExtended.