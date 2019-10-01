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
    ;; [`(,(? aexp?) ,(? aexp?)) #t]
    ;; [`(,(? aexp?) ,(? cexp?)) #t]
    ;; [`(,(? cexp?) ,(? aexp?)) #t]
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

;; small step state transition
;; greek aplhabet varsigma is usually used as "state"
(define (step-cc ς)
  ;; (displayln st)
  (match ς
    ;; if both value, do beta reduce
    [`(((λ (,x) ,em) ,(? aexp? v)) ,k)
     (displayln (subst em x v))
     `(,(subst em x v) ,k)]
    ;; if redex is evaled, put it into the hole
    [`(,(? aexp? v) ((HOLE ,en) . ,e))
     `((,v ,en) ,e)]
    [`(,(? aexp? v) ((,eu HOLE) . ,e))
     `((,eu ,v) ,e)]
    ;; if left is value, then set right as redex
    [`(((,(? aexp? v1)) ,(? cexp? em)) ,k)
     `(,em ,(cons `(,v1 HOLE) k))]
    ;; if m and n both not evaled, create a redex
    [`((,(? cexp? em) ,(? cexp? en)) ,k)
     `(,em ,(cons `(HOLE ,en) k))]
    [else
     (displayln "reach normal form")
     #f]
    ))

(define (multistep-cc ς)
  (let ([next (step-cc ς)])
    (displayln (format "step to --> ~s" next))
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
 (inject-cc (churchify '((λ (x) (if #t 1 0)) 1))))

;; test output:

;; the init state is (((λ (x) (((λ (t) (λ (f) t)) (λ (_) (λ (f) (λ (x) (f x))))) (λ (_) (λ (f) (λ (x) x))))) (λ (f) (λ (x) (f x)))) HOLE)
;; (((λ (t) (λ (f) t)) (λ (_) (λ (f) (λ (x) (f x))))) (λ (_) (λ (f) (λ (x) x))))
;; step to --> ((((λ (t) (λ (f) t)) (λ (_) (λ (f) (λ (x) (f x))))) (λ (_) (λ (f) (λ (x) x)))) HOLE)
;; step to --> (((λ (t) (λ (f) t)) (λ (_) (λ (f) (λ (x) (f x))))) ((HOLE (λ (_) (λ (f) (λ (x) x)))) . HOLE))
;; (λ (f) (λ (_) (λ (f) (λ (x) (f x)))))
;; step to --> ((λ (f) (λ (_) (λ (f) (λ (x) (f x))))) ((HOLE (λ (_) (λ (f) (λ (x) x)))) . HOLE))
;; step to --> (((λ (f) (λ (_) (λ (f) (λ (x) (f x))))) (λ (_) (λ (f) (λ (x) x)))) HOLE)
;; (λ (_) (λ (f) (λ (x) (f x))))
;; step to --> ((λ (_) (λ (f) (λ (x) (f x)))) HOLE)
;; reach normal form
;; step to --> #f
;; '(λ (_) (λ (f) (λ (x) (f x))))


