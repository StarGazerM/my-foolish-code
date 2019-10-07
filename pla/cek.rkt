;; Yihao Sun <ysun67@syr.edu>
;; 2019 Syracuse
#lang racket
(require "./church.rkt")

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

;; in SCC machine we can find everything we are actually dealing with
;; inner most application. Which means transition always acess context
;; from the innside and in a last-in, first-out facshion.
;; we can define a list like data structure called continuation. and in
;; order to make it readable, inverting the list into primitive application

;; define continuation
(define (kont? k)
  (match k
    ;; empty hole
    ['mt #t]
    [`(fun ,(? aexp?) ,(? kont?)) #t]
    [`(arg ,(? cexp?) ,(? kont?)) #t]))

;; modify SCC machine
(define (step-ck ς)
  (match ς
    [`((,(? cexp? em) ,(? cexp? en)) ,(? kont? k))
     `(,em (arg ,en ,k))]
    ;; if fun is evaled, switch redex to argument
    [`(,(? aexp? v) (arg ,en ,k))
     `(,en (fun ,v ,k))]
    ;; arg and fun are both evaled, perform application
    [`(,(? aexp? v) (fun (λ (,x) ,em) ,k))
     `(,(subst em x v) ,k)]
    [else
     (displayln "reach end")
     #f]
    ))

;; inject
(define (inject-ck e)
  `(,e mt))

(define (multistep-ck ς)
  (let ([next (step-ck ς)])
    (displayln (format "ck--> ~s" next))
    (if next
        (multistep-ck next)
        ς)))

;; specify valid value
(define (eval-ck ς)
  (displayln (format "the init state is ~s" ς))
  (let ([norm (multistep-ck ς)])
    (match norm
      [`(,(? aexp? b) mt) b]
      [else (error (format "stuck at ill form ~s" norm))])))

;; test ck machine
(eval-ck
 (inject-ck '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

;; the init state is ((((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m))) mt)
;; ck--> (((λ (x) x) (λ (y) y)) (arg ((λ (z) z) (λ (m) m)) mt))
;; ck--> ((λ (x) x) (arg (λ (y) y) (arg ((λ (z) z) (λ (m) m)) mt)))
;; ck--> ((λ (y) y) (fun (λ (x) x) (arg ((λ (z) z) (λ (m) m)) mt)))
;; ck--> ((λ (y) y) (arg ((λ (z) z) (λ (m) m)) mt))
;; ck--> (((λ (z) z) (λ (m) m)) (fun (λ (y) y) mt))
;; ck--> ((λ (z) z) (arg (λ (m) m) (fun (λ (y) y) mt)))
;; ck--> ((λ (m) m) (fun (λ (z) z) (fun (λ (y) y) mt)))
;; ck--> ((λ (m) m) (fun (λ (y) y) mt))
;; ck--> ((λ (m) m) mt)
;; reach end
;; ck--> #f
;; '(λ (m) m)

;; substitution and retraversal is can be complicate and give us
;; a lot of intermidiate value, we can eliminate this by delay
;; the evaluation.
;; we can introduce evironment and closure

;; define environment,in which all key is var and all value is
;; closure
;; closue is a pair the first is a open term and the second is
;; a environment make it close
(define (clo? c)
  (match c
    ;; we don't check whether term is closed
    [`(,(? cexp?) ,(? hash?)) #t]
    [else #f]))

;; TODO: env is not checked here
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

;; test cek machine
(eval-cek
 (inject-cek '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

;; the init state is (((((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m))) #hash()) mt)
;; cek--> ((((λ (x) x) (λ (y) y)) #hash()) (arg (((λ (z) z) (λ (m) m)) #hash()) mt))
;; cek--> (((λ (x) x) #hash()) (arg ((λ (y) y) #hash()) (arg (((λ (z) z) (λ (m) m)) #hash()) mt)))
;; cek--> (((λ (y) y) #hash()) (fun ((λ (x) x) #hash()) (arg (((λ (z) z) (λ (m) m)) #hash()) mt)))
;; cek--> ((x #hash((x . ((λ (y) y) #hash())))) (arg (((λ (z) z) (λ (m) m)) #hash()) mt))
;; cek--> (((λ (y) y) #hash()) (arg (((λ (z) z) (λ (m) m)) #hash()) mt))
;; cek--> ((((λ (z) z) (λ (m) m)) #hash()) (fun ((λ (y) y) #hash()) mt))
;; cek--> (((λ (z) z) #hash()) (arg ((λ (m) m) #hash()) (fun ((λ (y) y) #hash()) mt)))
;; cek--> (((λ (m) m) #hash()) (fun ((λ (z) z) #hash()) (fun ((λ (y) y) #hash()) mt)))
;; cek--> ((z #hash((z . ((λ (m) m) #hash())))) (fun ((λ (y) y) #hash()) mt))
;; cek--> (((λ (m) m) #hash()) (fun ((λ (y) y) #hash()) mt))
;; cek--> ((y #hash((y . ((λ (m) m) #hash())))) mt)
;; cek--> (((λ (m) m) #hash()) mt)
;; reach end
;; cek--> #f
;; '(λ (m) m)

;; in cek machine, the environment of each continuation is directly stored in itself
;; or in another word , environment and closure are mutually recursive.
;; we can seperate them using an external "storage", now our state become <C,E,S,K>
;; so this version of abstract machine is calle CESK machine

;; storage is a partial map from address to value. When we have address we only
;; need to store address rather than  real value in environment.(this also means
;; value will not appear inside continuation)

;; let's define CESK state transit step
;; NOTE: use σ for storage. and the actully state is <(C E) S K>
(define (step-cesk ς)
  (match ς
    [`(((,(? cexp? e0) ,(? cexp? e1))
        ,(? hash? ρ))
       ,(? hash? σ)
       ,(? ekont? k))
     ; =>
     `((,e0 ,ρ)
       ,σ
       (arg (,e1 ,ρ) ,k))]
    [`((,(? symbol? x) ,(? hash? ρ))
       ,(? hash? σ)
       ,(? ekont? k))
     ; =>
     `(,(hash-ref σ (hash-ref ρ x)) ,σ ,k)]
    [`((,(? aexp? v) ,(? hash? ρ))
       ,(? hash? σ)
       (arg (,(? cexp? e) ,(? hash? ρ-prime)) ,(? ekont? k)))
     ; =>
     `((,e ,ρ-prime)
       ,σ
       (fun (,v ,ρ) ,k))]
    [`((,(? aexp? v) ,(? hash? ρ))
       ,(? hash? σ)
       (fun ((λ (,x) ,e) ,(? hash? ρ-prime)) ,(? ekont? k)))
     ; =>
     ;; allocate a address "a" for the calculated value, and then
     ;; put the value to env
     (let ([a (gensym)])
       `((,e ,(hash-set ρ-prime x a))
         ,(hash-set σ a `(,v ,ρ))
         ,k))]
    [else
     (displayln "reach end")
     #f]
    ))

;; inject
(define (inject-cesk e)
  `((,e ,(hash)) ,(hash) mt))

(define (multistep-cesk ς)
  (let ([next (step-cesk ς)])
    (displayln (format "cesk--> ~s" next))
    (if next
        (multistep-cesk next)
        ς)))

;; specify valid value
(define (eval-cesk ς)
  (displayln (format "the init state is ~s" ς))
  (let ([norm (multistep-cesk ς)])
    (match norm
      [`((,(? aexp? b) ,(? hash?)) ,(? hash?) mt) b]
      [else (error (format "stuck at ill form ~s" norm))])))

;; test cesk machine
(eval-cesk
 (inject-cesk '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

