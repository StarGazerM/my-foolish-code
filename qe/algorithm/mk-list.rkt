#lang racket

(require cKanren/miniKanren)
(require cKanren/neq)

(define nullₒ
  (λ (l) (== l '())))

(define carₒ
  (λ (l x)
    (fresh (xs)
      (== `(,x . ,xs) l))))

(define cdrₒ
  (λ (l xs)
    (fresh (x)
      (== `(,x . ,xs) l))))

(define consₒ
  (λ (x xs l)
    (== `(,x . ,xs) l)))

(define appendₒ
  (λ (l s ls)
    (conde
      [(nullₒ l) (== s ls)]
      [(fresh (hl tl tls) 
        (== `(,hl . ,tl) l)
        (== `(,hl . ,tls) ls)
        (appendₒ tl s tls))])))

(define memberₒ
  (λ (x l)
    (conde
      [(fresh (hl)
        (carₒ l hl)
        (== x hl))]
      [(fresh (hl tl)
        (consₒ hl tl l)
        (=/= x hl)
        (memberₒ x tl))])))

(run 1 (x) (nullₒ x))
(run 1 (x) (carₒ '(1 2 3) x))
(run 1 (x) (cdrₒ '(1 2 3) x))
(run 1 (x) (appendₒ '(1 2 3) x '(1 2 3 4 5)))
(run* (x) (memberₒ x '(1 2 3)))

