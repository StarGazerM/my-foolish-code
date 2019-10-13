;; Yihao Sun <ysun67@syr.edu>
;; 2019 Syracuse
#lang racket

(require graphviz)
;; 0-cfa using abstracting abstract machine

(define DOT-template
  "digraph G {\n ~a }")
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
;; (define addr? symbol?)

;; alloc should be a partial map <ς, k> ⟶ Addr
;; (define alloc-map (hash))

;; 0-cfa is a context free analysis, if a function
;; for simplify I will only use the control string as address of continuation
;; and I will use the name of symbol for addr of var
(define (alloc ς k)
  (match ς
    [`(,c ,ρ ,σ ,a)
     (match k
       ;; distinguish the c by it's continuation
       [`(fun ,v ,ρ ,na) `(fn ,c)]
       [`(arg ,v ,ρ ,na) `(ar ,c)]
       ['mt `(mt ,c)])]
    [(? symbol? x) x]))
     ;; (if (hash-has-key? alloc-map `(,c ,k))
     ;;     (hash-ref alloc-map `(,c ,k))
     ;;     ;; if not exist create a new addr
     ;;     (let ([new-addr (gensym)])
     ;;       (set! alloc-map (hash-set alloc-map `(,c ,k) new-addr))
     ;;       new-addr))]))

(define (state-info ς)
  (match ς
    [`(,c ,ρ ,σ ,a)
     (match (first (hash-ref σ a))
       ;; distinguish the c by it's continuation
       [`(fun ,v ,ρ ,na) (format "~s_fn" c)]
       [`(arg ,v ,ρ ,na) (format "~s_ar" c)]
       ['mt (format "~s" c)])]))

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
  `(,e ,(hash) ,(hash 'hole  '(mt)) hole))

;; step function
;; choose particular value
;; in current semantic 
(define (step ς)
  (match ς
    ;; var
    [`(,(? symbol? x)
       ,(? hash? ρ)
       ,(? hash? σ)
       ,a)
     ; =>
     ;;(displayln (hash-ref σ (hash-ref ρ x)))
     (match (first (hash-ref σ (hash-ref ρ x)))
       [`(,(? aexp? v) ,(? hash? ρ-prime))
        `(,v ,ρ-prime ,σ ,a)])]
    ;; app
    [`((,(? cexp? e0) ,(? cexp? e1))
       ,(? hash? ρ)
       ,(? hash? σ)
       ,a)
     ; =>
     (let* ([k (first (hash-ref σ a))]
            [b (alloc ς k)])
       `(,e0 ,ρ ,(union σ b `(arg ,e1 ,ρ ,a)) ,b))]
    ;; value
    [`(,(? aexp? v) ,(? hash? ρ) ,(? hash? σ) ,a)
     (let ([k (first (hash-ref σ a))])
       (match k
         [`(arg ,e ,ρ-prime ,c)
          ; =>
          (let ([b (alloc ς k)])
            `(,e ,ρ-prime ,(union σ b `(fun ,v ,ρ ,c)) ,b))]
         [`(fun (λ (,x) ,e) ,ρ-prime ,c)
          ; =>
          (let (;; for simple, here will use var name directly
                ;; as address
                [b (alloc x k)])
            `(,e
              ,(hash-set ρ-prime x x)
              ,(union σ b `(,v ,ρ))
              ,c))]
         [else #f]))]
     [else #f]
     ))

;; muti step
;; when encouter a new state it will be add to result list
(define (multistep ς res graph)
  (let ([ς-prime (step ς)])
    (displayln "cesk*-->")
    (pretty-display ς-prime)
    ;;(pretty-display alloc-map)
    ;; check if rule can still apply
    (if ς-prime
        ;; if result set do not grow, fixpoint reached
        (if (member ς-prime res)
            (begin
              (displayln "fixpoint reached!")
              graph)
            (multistep ς-prime (cons ς-prime res)
                       (string-append
                        (format "    ~s -> ~s\n" (state-info ς) (state-info ς-prime))
                        graph)))
        graph)))

;; specify valid value
(define (evals ς)
  (displayln "the init state is")
  (pretty-display ς)
  (multistep ς '() ""));; test 
;; (evals
;;  (inject '((λ (f) (f f)) (λ (g) (g g)))))

;; gen graph viz
(display (evals (inject '((λ (f) (f f)) (λ (g) (g g))))))

(define (output)
  (define out (open-output-file "cfa.dot" #:exists 'truncate))
  (display (format DOT-template
                   (evals (inject '((λ (f) (f f)) (λ (g) (g g))))))
           out)
  (close-output-port out))

(output)
