#lang pie

;;------------------------------------------------------------------------------------------------------------
;; something have been cooked before~~
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

;; function length, calculate the length of list
(claim step-length
  (Π ((E U))
    (-> E (List E) Nat
       Nat)))
(define step-length
  (λ (E)
    (λ (e es length_es)
      (add1 length_es))))

(claim length
  (Π ((E U))
    (-> (List E)
       Nat)))
(define length
  (λ (E)
    (λ (es)
      (rec-List es
        0
        (step-length E)))))

;;----------------------------------------------------------------------------------------------------------------
;; let's make a fika
;; some funny data, emmmmm
(claim treats
  (Vec Atom 3))
(define treats
  (vec:: 'kanelbullar
    (vec:: 'plattar
      (vec:: 'prinsesstarta vecnil))))

(claim drinks
  (List Atom))
(define  drinks
  (:: 'coffee
    (:: 'cocoa nil)))

;; function list->vec
;; mot here is a type transfomer to define what type
;; we actually want
(claim mot-list->vec
  (Π ((E U))
    (-> (List E)
       U)))
(define mot-list->vec
  (λ (E)
    (λ (es)
      (Vec E (length E es)))))

;; almost answer in elminator, work like pattern match
;; and repack to type
(claim step-list->vec
  (Π ((E U)
           (e E)
           (es (List E)))
    (-> (mot-list->vec E es)
       (mot-list->vec E (:: e es)))))
(define step-list->vec
  (λ (E e es)
    (λ (list->vec_es)
      (vec:: e list->vec_es))))

(claim list->vec
  (Π ((E U)
           (es (List E)))
    (Vec E (length  E es))))
(define list->vec
  (λ (E es)
    (ind-List es
      (mot-list->vec E)
      vecnil
      (step-list->vec E))))

;; function vec append
;;  in our append logic we only care about first list
;;  so only "k" is used here. If j is to be used, we will be
;; force to retrun a λ which is unnecessary
(claim mot-vec-append
  (Π ((E U)
           (_j Nat)
           (k Nat))
    (-> (Vec E k)
       U)))
(define mot-vec-append
  (λ (E j k)
    (λ (_es)
      (Vec E (+ k j)))))

(claim step-vec-append
  (Π ((E U)
           (j Nat)
           (k Nat)
           (e E)
           (es (Vec E k)))
    (-> (mot-vec-append E j
            k es)
       (mot-vec-append E j
          (add1 k) (vec:: e es)))))
(define step-vec-append
  (λ (E j k e es)
    (λ (vec-append_es)
      (vec:: e vec-append_es))))

;; base case here is the other list we want to
;; append at the end
(claim  vec-append
  (Π ((E U)
           (l Nat)
           (j Nat))
    (-> (Vec E l) (Vec E j)
       (Vec E  (+ l j)))))
(define vec-append
  (λ (E l j)
    (λ (es end)
      (ind-Vec l es
        (mot-vec-append E j)
        end
        (step-vec-append E j)))))


;; function vec->list
(claim mot-vec->list
  (Π ((E U)
           (l Nat))
    (-> (Vec E l)
       U)))
(define mot-vec->list
  (λ (E l)
    (λ (es)
      (List E))))

(claim step-vec->list
  (Π ((E U)
           (l-1 Nat)
           (e E)
           (es (Vec E l-1)))
    (-> (mot-vec->list E
              l-1 es)
       (mot-vec->list E
         (add1 l-1) (vec:: e es)))))
(define step-vec->list
  (λ (E l-1 e es)
    (λ (vec->list_l-1)
      (:: e vec->list_l-1))))

(claim vec->list
  (Π ((E U)
           (l Nat))
    (-> (Vec E l)
       (List E))))
(define vec->list
  (λ (E l)
    (λ (es)
      (ind-Vec l es
        (mot-vec->list E)
        nil
        (step-vec->list E)))))

;; finally we can make a fika (TwT)P~
(claim fika
  (Vec Atom 5))
(define fika
  (vec-append Atom 3 2
    treats
    (list->vec Atom drinks)))

;; here we wish to verify  the correctness of append
;; because according to the type of list function
;; (it's also the type of some foolish function)
;; above the correctness of our fika can't be verified.
;; One way is check when it transformed back, it will
;; not change (OwO), naive but useful
(claim  list->vec->list=
  (Π ((E U)
           (es (List E)))
    (= (List E)
      es
      (vec->list E
        (length E es)
        (list->vec E es)))))

;; base case is easy ---- (same nil)

;; let's have the motive for our proof
;; the motive here is trans to the type we
;; interest, which is (=) type
(claim mot-list->vec->list=
  ( Π ((E U))
     (-> (List E)
        U)))
(define mot-list->vec->list=
  (λ (E es)
    (= (List E)
      es
      (vec->list E
        (length E es)
        (list->vec E es)))))

;; if we want to use induction, we want paritial use
;; (::)  as a function and  then we can really do somthing
;; similar to pattern match (:: e es)  to extract es out,
;; and then use "cong" we can eliminate "=" claim.
;; (es in n-1 step is needed to induct to n step)
(claim ::-fun
  (Π ((E U))
    (-> E (List E)
       (List E))))
(define ::-fun
  (λ (E)
    (λ (e es)
      (:: e es))))

(claim step-list->vec->list=
  (Π ((E U)
           (e E)
           (es (List E)))
    (-> (mot-list->vec->list= E
          es)
       (mot-list->vec->list= E
         (:: e es)))))
(define step-list->vec->list=
  (λ (E e es)
    (λ (list->vec->list_es)
      (cong list->vec->list_es
        (::-fun E e)))))

(define list->vec->list=
  (λ (E es)
    (ind-List es
      (mot-list->vec->list= E)
      (same nil)
      (step-list->vec->list= E))))

;; finally ......
;; Q.E.D.....die

;; have try.....

;; (list->vec->list= Atom
;;                    drinks)
;; (the (= (List Atom)
;;        (:: 'coffee
;;          (:: 'cocoa nil))
;;        (:: 'coffee
;;          (:: 'cocoa nil)))
;;   (same (:: 'coffee
;;           (:: 'cocoa nil))))


