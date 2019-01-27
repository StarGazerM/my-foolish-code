#lang pie

;; here is our old friend!!
;; Tirival is a new guy, it's a Type only has one
;; value--"sole"
;; sounds like a foolish "Null"......
(claim Maybe
  (-> U
     U))
(define Maybe
  (λ (X)
    (Either X Trivial)))

(claim nothing
  (Π ((E U))
    (Maybe E)))
(define nothing
  (λ (E)
    (right sole)))

(claim  just
  (Π ((E U))
    (-> E
       (Maybe E))))
(define just
  (λ (E e)
    (left e)))

;; let's play with our old friend
(claim maybe-head
  (Π ((E U))
    (-> (List E)
       (Maybe E))))
;; easy~ just recusive to the end, and in base case
;; return a nothing!
(define maybe-head
  (λ (E es)
    (rec-List es
      (nothing E)
      (λ (hd tl head_tl)
        (just E hd)))))

(claim  maybe-tail
  (Π ((E U))
    (-> (List E)
       (Maybe (List E)))))
(define maybe-tail
  (λ (E es)
    (rec-List es
      (nothing (List E))
      (λ (hd tl head_tl)
        (just (List E) tl)))))

;; boundary check
(claim list-ref
  (Π ((E U))
    (-> Nat (List E)
       (Maybe E))))

(claim step-list-ref
  (Π ((E U))
    (-> Nat
       (-> (List E)
          (Maybe E))
       (-> (List E)
          (Maybe E)))))
(define step-list-ref
  (λ (E)
    (λ (n-1 list_ref_n-1)
      (λ (es)
        (ind-Either (maybe-tail E es)
          (λ (maybe_tl)
            (Maybe E))
          (λ (tl)
            (list_ref_n-1 tl))
          (λ (empty)
            (nothing E)))))))

(define  list-ref
  (λ (E n)
    (rec-Nat n
      (maybe-head E)
      (step-list-ref E))))

;; -------------------------------------------------------------------------
;; whew~ another old friend Absurd~~

;; in orde to play with finite vec, we need a new type
;; Fin to describ a finity Nat whose upper bound is n.
(claim Fin
  (-> Nat
     U))
(define Fin
  (λ (n)
    (iter-Nat n
      Absurd
      Maybe)))
;; that's fancy
;; we are using a trick that the value number of Maybe,
;; is alway n+1 for a n-level Maybe ! it's a good measure.
;; (Maybe (Maybe (Maybe .....)))

;; if we want to pick a specific entry in our code, a little
;; more need to be done.

;; Let's see the first entry
;; yeah, add one,just means one more level Maybe! easy!
(claim fzero
  (Π ((n Nat))
    (Fin (add1 n))))
(define fzero
  (λ (n)
    (nothing (Fin n))))

;; some more
(claim fadd1
  (Π ((n Nat))
    (-> (Fin n)
       (Fin (add1 n)))))
(define fadd1
  (λ (n)
    (λ (i-1)
      (just (Fin n) i-1))))

;; now everything is prepared
(claim vec-ref
  (Π ((E U)
         (l Nat))
    (-> (Fin l) (Vec E l)
       E)))

;; ind-Abusrd can give us a value-like Abusrd.
(claim base-vec-ref
  (Π ((E U))
    (-> (Fin zero) (Vec E zero)
       E)))
(define base-vec-ref
  (λ (E)
    (λ (no-value-ever es)
      (ind-Absurd no-value-ever
        E))))

(claim step-vec-ref
  (Π ((E U)
          (l-1 Nat))
    (-> (-> (Fin l-1)
               (Vec E l-1)
             E)
       (-> (Fin (add1 l-1))
             (Vec E (add1 l-1))
             E))))
(define step-vec-ref
  (λ (E l-1)
    (λ (vec-ref_l-1)
      (λ (i es)
        (ind-Either i
          (λ (i)
            E)
          (λ (i-1)
            (vec-ref_l-1
              i-1 (tail es)))
          (λ (triv)
            (head es)))))))

(define vec-ref
  (λ (E l)
    (ind-Nat l
      (λ (k)
        (-> (Fin k) (Vec E k)
           E))
      (base-vec-ref E)
      (step-vec-ref E))))

;;now try this
(claim num-vec
  (Vec Nat 4))
(define num-vec
  (vec:: 1
    (vec:: 2
      (vec:: 3
        (vec:: 4 vecnil)))))


;; > (vec-ref Nat 4 (fzero 3) num-vec)
;; (the Nat 1)
;;> (vec-ref Nat 4 (fadd1 3 (fadd1 2 (fzero 1))) num-vec)
;; (the Nat 3)

;; yes, I know it is fool for  a long list......



