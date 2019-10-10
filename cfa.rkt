;; Yihao Sun <ysun67@syr.edu>
;; 2019 Syracuse
#lang racket

;; 0-cfa using abstracting abstract machine

;; define test language gramma

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

;; define abstract machine
;; using time-stamped CESK* machine

;; value here is a closure
(define (value? v)
  (match v
    [`(,(? aexp?) ,(? hash?)) #t]
    [else #f]))

;; define contuation
;; v is value, e is expression, ρ is env, c is pointer to next
(define (ekont? k)
  (match k
    ;; empty hole
    ['mt #t]
    ;; fn<v, c>
    [`(fun ,(? value?) ,(? symbol?)) #t]
    ;; ar<e, ρ, c>
    [`(arg ,(? cexp?) ,(? hash?) ,(? symbol?)) #t]
    [else #f]))

;; addr should be a symbol type
(define addr? symbol?)

;; alloc should be a partial map <ς, k> ⟶ Addr
(define alloc-map (hash))

(define (alloc ς k)
  (if (hash-has-key? alloc-map `(,ς ,k))
      (hash-ref alloc-map `(,ς ,k))
      ;; if not exist create a new addr
      (let ([new-addr (gensym)])
        (set! alloc-map (hash-set alloc-map `(,ς ,k) new-addr))
        new-addr)
      ))

;; union the value with same addr
;; or add new one to map
(define (union σ a v)
  (if (hash-has-key? σ a)
      (hash-set σ a (if (member (hash-ref σ a) v)
                         (append (hash-ref σ a) (list v))
                         (hash-ref σ a)))
      (hash-set σ a (list v))))

;; the state of the machine is <C E S K*>
;; C is control redex
;; E is environment which is var ⟶ addr
;; S is storage which is addr ⟶ (set of value/continuation)
;; K* is a pointer of next continuation

;; inject
(define (inject e)
  `(,e ,(hash) ,(hash '•  '(mt)) •))

;;step function
(define (step ς)
  (match ς
    ;; var
    [`(,(? symbol? x)
       ,(? hash? ρ)
       ,(? hash? σ)
       ,(? addr? a))
     ; =>
     ;;(displayln (hash-ref σ (hash-ref ρ x)))
     (match (first (hash-ref σ (hash-ref ρ x)))
       [`(,(? aexp? v) ,(? hash? ρ-prime))
        `(,v ,ρ-prime ,σ ,a)])]
    ;; app
    [`((,(? cexp? e0) ,(? cexp? e1))
       ,(? hash? ρ)
       ,(? hash? σ)
       ,(? addr? a))
     ; =>
     (let* ([k (first (hash-ref σ a))]
            [b (alloc ς k)])
       `(,e0 ,ρ ,(union σ b `(arg ,e1 ,ρ ,a)) ,b))]
    ;; value
    [`(,(? aexp? v) ,(? hash? ρ) ,(? hash? σ) ,(? addr? a))
     (let* ([k (first (hash-ref σ a))]
            [b (alloc ς k)])
       (match k
         [`(arg ,e ,ρ-prime ,c)
          ; =>
          `(,e ,ρ-prime ,(union σ b `(fun ,v ,ρ ,c)) ,b)]
         [`(fun (λ (,x) ,e) ,ρ-prime ,c)
          ; =>
          `(,e
            ,(hash-set ρ-prime x b)
            ,(union σ b `(,v ,ρ))
            ,c)]
         ['mt #f]))]
    [else #f]
    ))


(define (multistep ς)
  (let ([next (step ς)])
    (displayln "cesk*-->")
    (pretty-display next)
    ;;(pretty-display alloc-map)
    (if next
        (multistep next)
        ς)))

;; specify valid value
(define (evals ς)
  (displayln "the init state is")
  (pretty-display ς)
  (let ([norm (multistep ς)])
    (match norm
      [`(,(? aexp? b) ,(? hash? ρ) ,(? hash? σ) ,a)
       (if (equal? (hash-ref σ a) 'mt)
           b
           (error (format "stuck at ill form ~s" norm)))]
      [else (error (format "stuck at ill form ~s" norm))])))

;; test cesk machine
;; (evals
;;  (inject '(((λ (x) x) (λ (y) y)) ((λ (z) z) (λ (m) m)))))

(evals
 (inject '((λ (f) (f f)) (λ (g) (g g)))))


