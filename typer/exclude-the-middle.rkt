#lang pie
;; tertium non datur~~~
;; "Every statement is ture or false."

;; okkay, let's make a prove of it!
;; That's sounds impossible.......cause we can't give
;; an evidence....

;; let's try opposite way
;; the claim is false is false
(claim pem-not-false
  (Π ((X U))
    (-> (-> (Either X
                  (-> X
                     Absurd))
              Absurd)
           Absurd)))
(define pem-not-false
  (λ (X)
    (λ (pem-false)
      (pem-false
        (right
          (λ (x)
            (pem-false
              (left x))))))))

;; the trick is give a func pem-false, can be used in lambda
;; body when we constuct a Absurd.
;; Yes, it is much easier to prove something is "not", compare
;; to something is, beacuse we only need one "Abusrd-like"
;; example.

;; there is other statement, which can be either true or false,
;; they are calle decidable .
(claim Dec
  (-> U
     U))
(define  Dec
  (λ (X)
    (Either X
      (-> X
         Absurd))))







