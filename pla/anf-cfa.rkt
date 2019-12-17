;; this code is a AAM style CFA example for ANF-converted scheme style
;; lambda calculus, support `if` `letrec` `call/cc` and multi arguments lambda
;; most of code is from Kris Micinski's Syracuse CIS700 course homework
;; Yihao Sun <ysun67@syr.edu>
;; 2019 in Syracuse

#lang racket

(require racket/hash)
;; ANF Lambda calculus
;; Definition of core language

;; Atomic expressions
(define (aexpr? ae)
  (match ae
    ;; Variables
    [(? symbol? x) #t]
    ;; Literals
    [(? number? n) #t]
    ;; Booleans
    [(? boolean? b) #t]
    ;; Lambdas
    [`(lambda (,(? symbol? xs) ...) ,(? expr?)) #t]
    ;; first order continuation
    [(? kont?) #t]
    [else #f]))

;; Expression language
(define (expr? e)
  (match e
    ;; Function calls
    [`(,(? aexpr? ae0) ,(? aexpr? aes) ...) #t]
    ;; Let forms
    [`(let ([,x ,(? expr? e)]) ,(? expr? let-body)) #t]
    ;; Returns
    [(? aexpr? ae) #t]
    ;; If
    [`(if ,(? aexpr? econd) ,(? expr? et) ,(? expr? ef)) #t]
    ;; call/cc
    [`(call/cc (lambda (,(? symbol?)) ,(? expr?))) #t]
    ;; letrec
    [`(letrec ([,x ,(? expr? e)]) ,(? expr? let-body)) #t]
    [else #f]))

;; Literals
(define (lit? l)
  (or (number? l) (boolean? l)))


;; allocator function this is key of precision in AAM-style CFA
;; allocₖ(ς) : State → Addr
;; bellow is the allocator funtion for 0-CFA
;; in 0-CFA addrs is the syntax form of control string
(define (addr? κₐ) (expr? κₐ))
(define (alloc₀ ς)
  (match ς
    [`(,e ,ρ ,σ ,κₐ) e]))


;; ρ ∈ Env, Environments
(define (env? ρ)
  (and (andmap symbol? (hash-keys ρ))
       (andmap addr? (hash-values ρ))))

;; σ ∈ Sto, Store
(define (sto? σ)
  (and (andmap addr? (hash-keys σ))
       (andmap (lambda (vs)
                 (andmap (or/c kont? value?) (set->list vs)))
               (hash-values σ))))

;; Values are either literals or closures
(define (value? v)
  (match v
    [(? lit?) #t]
    [`(clo (lambda (,x) ,(? expr?)) ,(? env?)) #t]
    ;; continuation is a kind of value
    [(? kont?) #t]
    [else #f]))

;; Continuations forms
;; each continuation can be something has a pointer to next continuation
;; or empty continuation
(define (kont? k)
  (match k
    ['mt #t]
    [`(let ,(? symbol? x) ,(? env? ρ) ,(? expr? let-body) ,(? addr? k)) #t]
    [else #f]))

;; Definition of ς ∈ Σ ::= ⟨ C, E, S, K ⟩
;; K is a pointer to Kont in store
(define (state? state)
  (match state
    [`(,(? expr?) ,(? env?) ,(? sto?) ,(? addr?)) #t]
    [else #f]))

;; update operation of store
(define (store-update σ a v)
  (hash-set σ a (set-add (hash-ref σ a (set)) v)))
;; union a value set into store
(define (store-∪ σ a vs)
  (hash-set σ a (set-union (hash-ref σ a (set)) vs)))

;; Create a CESK state from a term e
(define (inject e)
  `(,e ,(hash) ,(hash '• 'mt) •))

;; Examples
(define id-id '(let ([x (lambda (x) x)]) (x x)))
(define omega '(let ([y (lambda (x) (x x))]) (y y)))
(define id-id-id-id '(let ([x (lambda (x) x)]) (let ([y (x x)]) (y y))))
(define if-f '(let ([x #t]) (if x 1 2)))
(define ccc '(let ([x 1])
               (call/cc (lambda (k)
                          (let ([y (k x)])
                            2)))))
(define rec '(letrec ([loop (lambda (x) (loop x))])
               (loop 0)))

;; the atomic expression evaluator. In CFA, each value should be
;; a set of possible value, This is
;; AEval(ae,ρ) : AExpr × Env × Sto → {Value}.
(define (aeval ae ρ σ)
  (match ae
    [(? number? n) (set n)]
    [(? boolean? b) (set b)]
    [(? symbol? x) (hash-ref σ (hash-ref ρ x))]
    [`(lambda (,x) ,e) (set `(clo ,ae ,ρ))]))


;; non-deterministic Step relation: Σ → {Σ}
(define (step ς)
  ;; (displayln "hasdf")
  ;; (pretty-print ς)
  (match ς
    ;; Handle a let: step into `e` while remembering (via the `let`
    ;; continuation) to go back and bind x within ρ before proceeding
    ;; to body and continuation k.
    [`((let ([,x ,e]) ,body) ,ρ ,σ ,κₐ)
     (let ([α (alloc₀ ς)])
       (set `(,e ,ρ ,(store-update σ α `(let ,x ,ρ ,body ,κₐ)) ,α)))]
    ;; letrec, assume e is a curified recursive function  do code transfer to
    ;; Y combinator, and Y combinator here should also in ANF style.
    ;; (U (λ (y) (λ (f)
    ;;              (f (λ (x) (((y y) f) x)))))
    [`((letrec ([,x ,e]) ,body) ,ρ ,σ ,κₐ)
     (set `((let ([,x (((lambda (U-x) (U-x U-x))
                        (lambda (Y-y) (lambda (Y-f)
                                        (Y-f (lambda (Y-x)
                                               (let ([Y-yy (Y-y Y-y)])
                                                 (let ([Y-yyf (Y-yy f)])
                                                   (Y-yyf Y-x))))))))
                       ,e)]) ,body) ,ρ ,σ ,κₐ))]
    ;; Handle `if` statement, first step into cond-expr if cond-expr is
    ;; boolean just return the relate side of branch, if number or lambda
    ;; throw type err, if var, eval it. Since the code has been ANF-converted
    ;; there is no complex expr in cond position
    [`((if ,(? aexpr? econd) ,(? expr? tbranch) ,(? expr? fbranch)) ,ρ ,σ ,κₐ)
     (set-map (aeval econd ρ σ)
              (λ (econdᵥ)
                (match (econdᵥ)
                  [#t `(,tbranch ,ρ ,σ ,κₐ)]
                  [#f `(,fbranch ,ρ ,σ ,κₐ)])))]
    ;; call/cc, step into body and make continuation bind to x
    ;; apply a countinutaion, and it only take one argument
    ;; it will give up current and jump back to call/cc point
    ;; [`((,(? kont? k-ap) ,ae) ,ρ ,k)
    ;;  `(,ae ,ρ ,k-ap)]
    [`((call/cc (lambda (,x) ,body)) ,ρ ,σ ,κₐ)
     (set (let ([α (alloc₀ ς)])
            ;; TODO: call site problem here
            `(,body ,(hash-set ρ x κₐ) ,σ ,κₐ)))]
    ;; Returns. You should specify how to handle when an atomic
    ;; expression is in return position. Because this is an A-Normal
    ;; Form language, the only return position will be the `let`
    ;; continuation.
    [`(,(? aexpr? ae) ,ρ ,σ ,κₐ )
     (let ([vs (hash-ref σ κₐ)]
           ;; step into a state by a value
           [step₁ (λ (v)
                    (match v
                      [`(let ,x ,ρ-prime ,e ,κₙ)
                       (let ([α (alloc₀ ς)])
                         `(,e ,(hash-set ρ-prime x α)
                              ,(store-∪ σ α (aeval ae ρ σ)) ,κₙ))]))])
       ;; diverge here
       (set-map vs step₁)
       )]
    ;; Application. Each is an atomic expression. Assume that ae0 will
    ;; evaluate to a closure. This means that `(aeval ae0 ρ σ) will
    ;; evaluate to something that matches something like `(clo (lambda
    ;; (,xs ...) ,e-body) ,ρ-prime ,σ).
    ;; if we intro call/cc, (aeval ae0 ρ σ) can also be a continuation
    [`((,ae0 ,aes ...) ,ρ ,σ ,κₐ)
     (set-map (aeval ae0 ρ σ)
              (λ (ae0ᵥ)
                (match ae0ᵥ
                  [(? kont? k-ap)
                   ;; continuation can only apply to one element
                   `(,(first aes) ,ρ ,σ ,k-ap)]
                  [`(clo (lambda (,xs ...) ,e-body) ,ρ-prime)
                   ;; eval in one time
                   (let ([env&stos
                          (foldl (lambda (x ae e&s)
                                   (match e&s
                                     [`(,env ,sto)
                                      (let ([α (alloc₀ ς)])
                                        `(,(hash-set env x α)
                                          ,(store-∪ sto α (aeval ae ρ σ)))
                                        )]))
                                 `(,ρ-prime ,σ) xs aes)])
                     (match env&stos
                       [`(,new-ρ ,new-σ) `(,e-body ,new-ρ ,new-σ ,κₐ)]))]
                  [else (error "LHS value is not a closure can't apply!")]
                  )))]
    ))

;; count abstract value inside of graph
(define (cnt-sto-vals g)
  (foldl (λ (avs) (length (set->list avs)))
         0 (hash->list (hash-values g))))

;; Is this state at a done configuration?
;; In CFA, if state in state graph doesn't increase
;; which means we have reach fixpoint, we are done
(define (done? state graph prev-graph)
  (if (equal? graph prev-graph)
      #t
      (match state
        [`(,(? aexpr?) ,ρ ,σ •) #t]
        [else #f])))

;; Iterate the state to a final answer, build up a transition graph.
(define (iterate state)
  (define (h state state-graph last-state prev-graph)
    ;; (displayln (format "new graph: ~a" (cnt-sto-vals state-graph)))
    ;; (pretty-print state-graph)
    ;; (displayln "old graph:")
    ;; (pretty-print prev-graph)
    (if (done? state state-graph prev-graph)
        (begin (displayln "Done!") (pretty-print state) state-graph)
        (let* ([next-states (set->list (step state))]
               ;; Add to the state graph by adding an edge between the
               ;; last state and this state.
               [next-state-graph
                (if (null? last-state)
                    (foldl (λ (ς g) (hash-set g ς (set))) state-graph next-states)
                    #;(hash-set state-graph next-state (set))
                    (foldl (λ (ς g)
                             (hash-set g last-state
                                       (set-add
                                        (hash-ref state-graph last-state (set)) ς)))
                           state-graph next-states)
                    #;(hash-set state-graph
                              last-state
                              (set-add (hash-ref state-graph last-state (set)) next-state)))])
          (displayln (format "--> ~a" (pretty-format state)))
          (foldl (λ (g res)
                   (hash-union g res #:combine/key (λ (k v₁ v₂) (set-union v₁ v₂))))
                 (hash)
                 (map (λ (ς) (h ς next-state-graph ς state-graph)) next-states)))))
  (h state (hash) null null))

;; get contol string
(define (state-control ς)
  (match ς
    [`(,c ,_ ,_ ,_) c]))

;; Render h as a DOT graph
(define (graphify h)
  (define lines
    (flatten
     (hash-map h
               (lambda (key value)
                 (map (lambda (v)
                        (format "\"~a\" -> \"~a\""
                                (state-control key) (state-control v)))
                      (set->list value))))))
  (displayln "digraph {")
  (for ([line lines])
    (displayln (format "  ~a" line)))
  (displayln "}"))

;;
;; REPL
;;

;; Run a REPL
(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    (if (expr? input)
        ;; Execute the expression
        (graphify (iterate (inject input)))
        (displayln "Input expression does not satisfy expr?"))
    (repl)))


;; some test case
;; (displayln "test for id-id")
;; (iterate (inject id-id))
;; (displayln ">>>>>>>>>>>>>>>>>>>>>>>>>>")
;; (displayln "test for id-id-id-id")
;; (graphify (iterate (inject id-id-id-id)))
;; (displayln ">>>>>>>>>>>>>>>>>>>>>>>>>>")
;; (graphify (iterate (inject omega)))
;; TODO: pass call/cc and if
;; (displayln ">>>>>>>>>>>>>>>>>>>>>>>>>>")
;; (displayln "test for call/cc")
;; (iterate (inject ccc))
;; (displayln ">>>>>>>>>>>>>>>>>>>>>>>>>>")
;; (display "test for if")
;; (iterate (inject if-f))

;; ;; Top level entry point to the program
;; (repl)

