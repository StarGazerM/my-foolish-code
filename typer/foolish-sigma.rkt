#lang pie

;; -----------------------------------------------------------------------------
;;function +, plus for Nat
(claim step-+
  (-> Nat
     Nat))
(define step-+
  (λ (+_n-1)
    (add1 +_n-1)))

(claim +
  (-> Nat Nat
     Nat))
(define +
  (λ (n j)
    (iter-Nat n
      j
      step-+)))

;; here is some foolish preparation for my
;; foolish code
;; oh, a strange double, TvT, I know it's fool
;; but we can get a value through this double,
;; cause it have a (add1 ) on the top in it's
;; normal form.
;; basicaly, it's just replace "(add ...)" with
;; (add1 (add1 ....)
(claim double
  (-> Nat
     Nat))
(define double
  (λ (n)
    (iter-Nat n
      0
      (+ 2))))

;; -------------------------------------------------------------------------------------
;; let's try to written  even number as type~
;; Even is defined by "there exists" so let's
;; use "Σ"....
(claim Even
  (-> Nat U))
(define Even
  (λ (n)
    (Σ ((half Nat))
      (= Nat n (double half)))))

;; cool, like a pair to state a Even
;; (car even_n) is the half of a  Even number
;; (cdr even_n) is it's value

;; foolish define is not enough, we need some
;; proof using rule of Σ (cons)

;; eg for 0~
(claim zero-is-even
  (Even 0))
(define  zero-is-even
  (cons 0
    (same 0)))

;; safe~
;; let's try to  proove something harder
;; (Even + 2) is still an even
;; there is every logic here, of course a "Π"
(claim +two=even
  (Π ((n Nat))
    (-> (Even n)
       (Even (+ 2 n)))))
;; if  e_n is  a even number,
;; what we need is just to check if
;; (half+1) * 2 = en+2
;; yeah sate it.
(define +two=even
  (λ (n e_n)
    (cons (add1 (car e_n))
      (cong (cdr e_n) (+ 2)))))

;; Oh, now we can prove other even number
;; are "(Even ...)"
(claim  two-is-even
  (Even 2))
(define two-is-even
  (+two=even 0 zero-is-even))

;; .........where is Odd
;; okkay I am not so foolish
;; haf is a little smaller than half
(claim  Odd
  (-> Nat
     U))
(define Odd
  (λ (n)
    (Σ ((haf Nat))
      (= Nat n (add1 (double haf))))))

;; even +1 should be an odd
(claim add1-even->odd
  (Π ((n Nat))
    (-> (Even n)
     (Odd (add1 n)))))
;; the difference is actually between "haf"
;; and "half" !!
;; smart!
(define add1-even->odd
  (λ (n e_n)
    (cons (car e_n)
      (cong (cdr e_n) (+ 1)))))

;; THIS IS A MIRROR  (OwO)
(claim add1-odd->even
  (Π ((n Nat))
    (-> (Odd n)
     (Even (add1 n)))))
(define add1-odd->even
  (λ (n o_n)
    (cons (add1 (car o_n))
      (cong (cdr o_n) (+ 1)))))

;; --------------------------------------------------------------------------------------------
;; just a repeat
(claim repeat
  (-> (-> Nat
         Nat)
     Nat
     Nat))
(define repeat
  (λ (f n)
    (iter-Nat n
      (f 1)
      (λ (iter_f_n-1)
           (f iter_f_n-1)))))

;; what's this !!!!!!!!!
(claim ackermann
  (-> Nat Nat
     Nat))
(define ackermann
  (λ (n)
    (iter-Nat n
      (+ 1)
      (λ (ackermann_n-1)
        (repeat ackermann_n-1)))))

;; ackermann is total!!! what!!!!

;; ---------------------------------------------------------------
;; emmmm
;; maybe it's the most complecated "Either" code I've ever seen!!!

;; fine, let's give a proof to a foolish statement
;; every Nat is Even or Double
;; easyyyyyyy!
;; 0 is even, and every add1 will make a change!
;; ind-Nat will help a lot here.
(claim even-or-odd
  (Π ((n Nat))
    (Either (Even n) (Odd n))))

;; base case is zero, zero is even

;; we want to do some calculate on Either, so
;; it is clear we need to match it's eliminator
;; our purpose is get the data inside (Even/Odd)
;; Oh ! it's prepared for iter EVERY Nat.
(claim mot-even-or-odd
  (-> Nat
     U))
(define mot-even-or-odd
  (λ (k)
    (Either (Even k) (Odd k))))

(claim step-even-or-odd
  (Π ((n-1 Nat))
    (-> (mot-even-or-odd n-1)
       (mot-even-or-odd (add1 n-1)))))
;; emmmm, actually we don't need mot here,
;; when we are consider eliminate Either level
;; we are not asking for some other type in this
;; case.
;; ha, that's foolish.
(define step-even-or-odd
  (λ (n-1)
    (λ (e-or-o_n-1)
      (ind-Either e-or-o_n-1
        (λ (e-or-o)
          (mot-even-or-odd (add1 n-1)))
        (λ (e_n-1)
          (right
            (add1-even->odd
              n-1 e_n-1)))
        (λ (o_n-1)
          (left
            (add1-odd->even
              n-1 o_n-1)))))))

;; get it!
(define even-or-odd
  (λ (n)
    (ind-Nat n
      mot-even-or-odd
      (left zero-is-even)
      step-even-or-odd)))


#|
> (even-or-odd 2)
(the (Either (Σ ((half Nat))
              (= Nat
                2
                (iter-Nat half
                   (the Nat 0)
                   (λ (j)
                     (add1 (add1 j))))))
       (Σ ((haf Nat))
        (= Nat
          2
          (add1 (iter-Nat haf
                   (the Nat 0)
                   (λ (j)
                     (add1 (add1 j))))))))
  (left (cons 1
          (same 2))))
|#
;; emmmmmmmm the type is long, read the value!!!
#|
(left (cons 1
          (same 2))))
|#
;; wow!!!!!!!!! it's an proved even number!













