;; Yihao Sun (ysun67@syr.edu)
;; Syracuse 2019
#lang racket

;; (require "./metacircular.rkt")
(require "./church.rkt")
;; This is a tiny example for using abstract interpret machine
;; using standard lambda calcli as target toy language
;; assume it is currified and church encoded

;; atomic expression
(define (aexp? e)
  (match e
    [(? symbol?) #t]
    [`(λ (,(? symbol?)) ,body) #t]
    [else #f]))

;; compound express
(define (cexp? e)
  (match e
    [(? aexp?) #t]
    [`(,(? cexp? f) ,(? cexp?)) #t]
    [else #f]
    ))

;; before I start CEK machine, let's look at a more simple env-redex
;; model called "CC" machine, which means current subterm of interests
;; and current evaluation context
;; CC machine is a state machine with a state pair <M,E>, M is the control
;; string and E is the context
;; the step means to find what is current interests (redex) and what is
;; contex, "hole" is the placeholder of interest in a context
;; <(M N), E> |-> <M, E[(HOLE N)>
;; notation E[...] means fill in the hole with some expr
;; I use k for E just make it different from "expression" in code ....

;; wrap a express into a CC machine state pair, before every thing start,
;; it is clear that every context is a hole
(define (inject-cc e)
  `(,e HOLE))

;; this machine is a substition based textual machine, so subst is need
(define (subst e x t)
  (match e
    ;; var
    [(? symbol? y) (if (equal? x y) t y)]
    ;; fun
    [`(λ (,(? symbol? y)) ,body)
     (if (equal? x y)
         e
         `(λ (,y) ,(subst body x t)))]
    ;; app
    [`(,(? cexp? e1) ,(? cexp? e2))
     `(,(subst e1 x t) ,(subst e2 x t))]))

;; fill in the hole of e1 with e2
(define (fill e1 e2)
  ;; there should be only one hole, although the efficiency is low here
  (match e1
    ['HOLE
     e2]
    [`(,l ,r)
     `(,(fill l e2) ,(fill r e2))]
    [else e1]))

;; small step state transition
;; greek aplhabet varsigma is usually used as "state"
(define (step-cc ς)
  (match ς
    ;; if both value, do beta reduce
    [`(((λ (,x) ,em) ,(? aexp? v)) ,k)
     `(,(subst em x v) ,k)]
    ;; if redex is evaled, take out the application which contain hole
    ;; v in left
    ;; hole with nothing left
    [`(,(? aexp? v) (HOLE ,en))
     `((,v ,en) HOLE)]
    ;; hole in left
    [`(,(? aexp? v) ((HOLE ,en) ,k))
     `((,v ,en) ,k)]
    ;; hole in right
    [`(,(? aexp? v) (,k (HOLE ,en)))
     `((,v ,en) ,k)]
    ;; v in right
    ;; hole with nothing left
    [`(,(? aexp? v) (,eu HOLE))
     `((,eu ,v) HOLE)]
    ;; hole in left
    [`(,(? aexp? v) ((,eu HOLE) ,k))
     `((,eu ,v) ,k)]
    ;; hole in right
    [`(,(? aexp? v) (,k (,eu HOLE)))
     `((,eu ,v) ,k)]
    ;; if left is value, then set right as redex
    [`((,(? aexp? v1) ,(? cexp? em)) ,k)
     `(,em ,(fill k `(,v1 HOLE)))]
    ;; if m and n both not evaled, create a redex
    [`((,(? cexp? em) ,(? cexp? en)) ,k)
     `(,em ,(fill k `(HOLE ,en)))]
    [else
     (displayln "reach end")
     #f]))

(define (multistep-cc ς)
  (let ([next (step-cc ς)])
    (displayln (format " --> ~s" next))
    (if next
        (multistep-cc next)
        ς)))

;; specify valid value
(define (eval-cc ς)
  (displayln (format "the init state is ~s" ς))
  (let ([norm (multistep-cc ς)])
    (match norm
      [`(,(? aexp? b) HOLE) b]
      [else (error (format "stuck at ill form ~s" norm))])))

;; test cc machine
(eval-cc
 (inject-cc '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

;; test output:

;; the init state is ((((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m))) HOLE)
;; --> (((λ (x) x) (λ (y) y)) (HOLE ((λ (z) z) (λ (m) m))))
;; --> ((λ (y) y) (HOLE ((λ (z) z) (λ (m) m))))
;; --> (((λ (y) y) ((λ (z) z) (λ (m) m))) HOLE)
;; --> (((λ (z) z) (λ (m) m)) ((λ (y) y) HOLE))
;; --> ((λ (m) m) ((λ (y) y) HOLE))
;; --> (((λ (y) y) (λ (m) m)) HOLE)
;; --> ((λ (m) m) HOLE)
;; reach end
;; --> #f
;; '(λ (m) m)

;; in CC Machine, we can easily notice that in case
;; <V, E[((λX.M) [])]>
;; this is actually the only possible case for <V, E[(U [])]>, in my toy
;; language if U is evaled, the only case is  function. Meanwhile consider if
;; we allow bool and int in lang, these term will get stuck eventually. So
;; we can already apply substition, there is no need for pull lambda out
;; then do subst. these two rule can be merged to one.
;; this modified version of machine is called SCC machine

(define (step-scc ς)
  (match ς
    ;; in scc machine we should't exclude value case
    [`((,(? cexp? em) ,(? cexp? en)) ,k)
     `(,em ,(fill k `(HOLE ,en)))]
    ;; if redex is evaled, switch redex from v n to make it form can be evaled
    ;; v in left
    ;; hole with nothing left
    [`(,(? aexp? v) (HOLE ,en))
     `(,en (,v HOLE))]
    ;; hole in left
    [`(,(? aexp? v) ((HOLE ,en) ,k))
     `(,en ((,v HOLE) ,k))]
    ;; hole in right
    [`(,(? aexp? v) (,k (HOLE ,en)))
     `(,en (,k (,v HOLE)))]
    ;; v in right, leftside should only be lambda with HOLE
    ;; hole with nothing left
    [`(,(? aexp? v) ((λ (,x) ,em) HOLE))
     `(,(subst em x v) HOLE)]
    ;; hole in left
    [`(,(? aexp? v) (((λ (,x) ,em) HOLE) ,k))
     `(,(subst em x v) (HOLE ,k))]
    ;; hole in right
    [`(,(? aexp? v) (,k ((λ (,x) ,em) HOLE)))
     `(,(subst em x v) (,k HOLE))]
    [else
     (displayln "reach end")
     #f]
    ))

(define (multistep-scc ς)
  (let ([next (step-scc ς)])
    (displayln (format "s--> ~s" next))
    (if next
        (multistep-scc next)
        ς)))

;; specify valid value
(define (eval-scc ς)
  (displayln (format "the init state is ~s" ς))
  (let ([norm (multistep-scc ς)])
    (match norm
      [`(,(? aexp? b) HOLE) b]
      [else (error (format "stuck at ill form ~s" norm))])))

;; inject function should be the same

;; test cc machine
(eval-scc
 (inject-cc '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

;; test output
;; '(λ (m) m)
;; the init state is ((((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m))) HOLE)
;; s--> (((λ (x) x) (λ (y) y)) (HOLE ((λ (z) z) (λ (m) m))))
;; s--> ((λ (x) x) ((HOLE (λ (y) y)) ((λ (z) z) (λ (m) m))))
;; s--> ((λ (y) y) (((λ (x) x) HOLE) ((λ (z) z) (λ (m) m))))
;; s--> ((λ (y) y) (HOLE ((λ (z) z) (λ (m) m))))
;; s--> (((λ (z) z) (λ (m) m)) ((λ (y) y) HOLE))
;; s--> ((λ (z) z) ((λ (y) y) (HOLE (λ (m) m))))
;; s--> ((λ (m) m) ((λ (y) y) ((λ (z) z) HOLE)))
;; s--> ((λ (m) m) ((λ (y) y) HOLE))
;; s--> ((λ (m) m) HOLE)
;; reach end
;; s--> #f
;; '(λ (m) m)

