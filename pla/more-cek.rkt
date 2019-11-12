;; Yihao Sun <ysun67@syr.edu>
;; 2019 Syracuse

#lang racket

;; using churchified  lambda calculis as example
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

(define (clo? c)
  (match c
    ;; we don't check whether term is closed
    [`(,(? cexp?) ,(? hash?)) #t]
    [else #f]))

(define (env? ρ)
  (and
   ;; all key should be symbol
   (andmap symbol? (hash-keys ρ))
   (andmap clo? (hash-values ρ))))

(define (value? v)
  (match v
    [`(,(? aexp?) ,(? hash?)) #t]
    [else #f]))

;; continuation with environment
(define (ekont? k)
  (match k
    ;; empty hole
    ['mt #t]
    [`(fun ,(? value?) ,(? ekont?)) #t]
    [`(arg ,(? clo?) ,(? ekont?)) #t]
    [else #f]))

;; step of cek machine
;; here for simplification I actually use <(c e) k> as my state
(define (step-cek ς)
  (match ς
    ;; compare to ck machine we add env to a control string
    [`(((,(? cexp? em) ,(? cexp? en))
        ,(? hash? ρ))
       ,(? ekont? k))
     ; =>
     `((,em ,ρ) (arg (,en ,ρ) ,k))]
    ;; eval a var, look it up in env
    [`((,(? symbol? x)
        ,(? hash? ρ))
       ,(? ekont? k))
     ; =>
     `(,(hash-ref ρ x) ,k)]
    ;; if fun is evaled, switch redex to argument
    [`((,(? aexp? v)
        ,(? hash? ρ))
       (arg (,en ,ρ-prime) ,(? ekont? k)))
     ; =>
     `((,en ,ρ-prime) (fun (,v ,ρ) ,k))]
    ;; we change subst to modify env
    [`((,(? aexp? v)
        ,(? hash? ρ))
       (fun ((λ (,x) ,em) ,(? hash? ρ-prime)) ,(? ekont? k)))
     ; =>
     `((,em ,(hash-set ρ-prime x `(,v ,ρ))) ,k)]
    [else
     (displayln "reach end")
     #f]
    ))

;; inject
(define (inject-cek e)
  `((,e ,(hash)) mt))

(define (multistep-cek ς)
  (let ([next (step-cek ς)])
    (displayln (format "cek--> ~s" next))
    (if next
        (multistep-cek next)
        ς)))

;; specify valid value
(define (eval-cek ς)
  (displayln (format "the init state is ~s" ς))
  (let ([norm (multistep-cek ς)])
    (match norm
      [`((,(? aexp? b) ,(? hash?)) mt) b]
      [else (error (format "stuck at ill form ~s" norm))])))

(eval-cek
 (inject-cek '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

