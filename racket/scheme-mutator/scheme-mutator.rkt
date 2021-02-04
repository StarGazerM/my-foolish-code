;; the racket scheme code random mutator

;; Yihao Sun
;; Syracuse 2020

#lang racket

(require "scheme-generator.rkt")
(require "scheme-lang.rkt")

;; is "node" a ast under grammar "g" ? 
#;(define (ast? g ast)
  (define )
  (match ast
    [`()]))

;; count how many node in a scheme ast
(define (count-ast s)
  (match s
    ['() 0]
    [(? prim?) 1]
    [(? symbol?) 1]
    [(? number?) 1]
    [(? boolean?) 1]
    [`(lambda (,xs ...) ,body)
     (+ (length xs) (count-ast body) 1)]
    [`(quote (,es ...)) (add1 (apply + (map count-ast es)))]
    [`(define ,x ,body) (add1 (+ 1 (count-ast body)))]
    [`(define (,xs ...) ,body)
     (add1 (+ (length xs) (count-ast body)))]
    [`(if ,eguard ,et ,ef)
     (add1 (+ (count-ast eguard) (count-ast et) (count-ast ef)))] 
    [`(let ((,names ,binds) ...) ,body)
     (add1 (+ (length names) (apply + (map count-ast binds)) (count-ast body)))]
    [`(,func ,args ...)
     (add1 (+ (count-ast func) (apply + (map count-ast args))))]))

(define (expand-s grammar token-map top depth)
  (string->sexpr (first (grammar-fuzz grammar token-map top 1))))


;; random choose a node from AST
;; generate random place "on-which", walk through AST until find that node
;; randomly generate a new node which has the same type as original node
(define (random-mutate scheme grammar token-map) 
  (define on-which (random 0 (count-ast scheme)))
  (define depth (random 10 20))
  (displayln (format "mutate on ~a" on-which))
  (define (helper s counter)
    ;;(displayln s)
    (let/ec return
    (match s
      [(? prim?) (expand-s grammar token-map 'PRIM depth)]
      [(? symbol?) (expand-s grammar token-map '%SYM depth)]
      [(? number?) (expand-s grammar token-map '%NUM depth)]
      [(? boolean?) (expand-s grammar token-map '%BOOL depth)]
      [`(lambda (,xs ...) ,body)
       (displayln (format "in function now the counter is ~a" counter))
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'FUN depth)))
       (let* ([new-counter&xs
               (for/fold ([counter&xs `(,counter ())])
                         ([x xs])
                 (if (equal? (add1 (first counter&xs)) on-which)
                     `(,(add1 (first counter&xs))
                       ,(append (second counter&xs)
                                (expand-s grammar token-map '%SYM depth)))
                     `(,(add1 (first counter&xs))
                       ,(append (second counter&xs) `(,x)))))]
              [new-body
               (cond
                 [(equal? (add1 (first new-counter&xs)) on-which)
                  (expand-s grammar token-map 'EXPR depth)]
                 [(and (< (first new-counter&xs) on-which)
                       (>= (+ (first new-counter&xs) (count-ast body)) on-which))
                  (helper body (add1 (first new-counter&xs)))]
                 [else body])])
         `(lambda ,(second new-counter&xs) ,new-body))]
      [`(quote (,es ...)) 
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'DATUM depth)))
       (define-values (new-es new-counter)
         (for/fold ([res '()]
                    [nc counter])
                   ([e es])
           (cond
             [(equal? (add1 nc) on-which)
              (define gtype
                (match e
                  [(? aexpr?) 'AEXPR]
                  [(? expr?) 'EXPR]))
              (values (append res (list (expand-s grammar token-map gtype depth)))
                      (add1 nc))]
             [else
              (values (append res (list e)) (add1 nc))])))
       `(quote ,new-es)]
      [`(define ,x ,body)
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'DEF depth)))
       (define counter-after-x  (add1 counter))
       (define new-x
         (cond
           [(equal? (add1 counter) on-which)
            (expand-s grammar token-map '%SYM depth)]
           [else x]))
       (define new-body
         (cond
           [(equal? (add1 counter-after-x) on-which)
            (expand-s grammar token-map 'EXPR depth)]
           [(and (< counter-after-x on-which)
                 (>= (+ counter-after-x (count-ast body))))
            (helper body (add1 counter-after-x))]
           [else body]))
       `(define ,new-x ,new-body)]
      [`(define (,xs ...) ,body)
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'DEF depth)))
       (define new-counter&xs
         (for/fold ([res `(,counter ,xs)])
                   ([x xs])
           `(,(add1 (first res))
             ,(append (second res)
                      (cond
                        [(equal? (add1 (first res)) on-which)
                         (expand-s grammar token-map '%SYM depth)]
                        [else x])))))
       (define new-body
         (cond
           [`(equal? (add1 (first new-counter&xs)))
            (expand-s grammar token-map 'EXPR depth)]
           [else body]))
       `(define ,(second new-counter&xs) ,new-body)]
      [`(if ,eguard ,et ,ef)
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'IF depth)))
        (define new-eguard
          (cond
            [(equal? (+ 1 counter) on-which)
             (expand-s grammar token-map 'EXPR depth)]
            [(and (< counter on-which)
                  (>= (+ (count-ast eguard) counter) on-which))
             (helper eguard (add1 counter))]
            [else eguard]))
        (define new-et
          (cond
            [(equal? (+ 1 (count-ast eguard) counter) on-which)
             (expand-s grammar token-map 'EXPR depth)]
            [(and (< (+ (count-ast eguard) counter) on-which)
                  (>= (+ (count-ast et) (count-ast eguard) counter) on-which))
             (helper et (+ counter (count-ast eguard)))]
            [else et]))
        (define new-ef
          (cond
            [(equal? (+ 1 (count-ast eguard) (count-ast et) counter) on-which)
             (expand-s grammar token-map 'EXPR depth)]
            [(and (< (+ (count-ast eguard) (count-ast et) counter) on-which)
                  (>= (+ (count-ast eguard) (count-ast et) (count-ast ef) counter) on-which))
             (helper ef (+ counter (count-ast eguard) (count-ast et)))]
            [else ef]))
        `(if ,new-eguard ,new-et ,new-ef)] 
      [`(let ((,names ,binds) ...) ,body)
       (displayln (format "in let now the count is ~a" counter))
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'LET depth)))
       (define-values (counter-after-names new-names)
         (for/fold ([nc counter]
                    [nn '()])
                   ([name (in-list names)])
           (values (add1 nc)
                   (cond
                     [(equal? (add1 nc) on-which)
                      (append nn (list (expand-s grammar token-map '%SYM depth)))]
                     [else (append nn (list name))]))))
       (displayln (format "in let after names now the counter is ~a" counter-after-names))
       (define-values (counter-after-binds new-binds)
         (for/fold ([nc counter-after-names]
                    [nb '()])
                   ([b (in-list binds)])
           (values (+ (count-ast b) nc)
                   (cond
                     [(equal? (add1 nc) on-which)
                      (append nb (list (expand-s grammar token-map 'EXPR depth)))]
                     [(and (< nc on-which)
                           (>= (+ (count-ast b) nc) on-which))
                      (append nb (list (helper b (add1 nc))))]
                     [else (append nb (list b))]))))
       (displayln (format "in let after binds now the counter is ~a" counter-after-binds))
       (define new-body
         (cond
           [(equal? (add1 counter-after-binds) on-which)
            (expand-s grammar token-map 'EXPR depth)]
           [(and (< counter-after-binds on-which)
                 (>= (+ counter-after-binds (count-ast body)) on-which))
            (helper body (add1 counter-after-binds))]
           [else body]))
       `(let ,(foldl (λ (n b res)
                       (append res `((,n ,b))))
                     '()
                     new-names
                     new-binds)
          ,new-body)]
      [`(,(? prim? prim) ,args ...)
       (displayln (format "in application now the counter is ~a" counter))
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'APP_PRIM depth)))
       (define new-prim
         (cond
           [(equal? (add1 counter) on-which)
            (expand-s grammar token-map 'PRIM depth)]
           [else prim]))
       (define-values (new-counter new-args)
         (for/fold ([nc (add1 counter)]
                    [na '()])
                   ([arg args])
           (values (+ nc (count-ast arg))
                   (append
                    na
                    (list (cond
                            [(equal? (+ 1 nc) on-which)
                             (expand-s grammar token-map 'EXPR depth)]
                            [(and (< nc on-which)
                                  (>= (+ (count-ast arg) nc) on-which))
                             (helper arg (+ counter (count-ast arg)))]
                            [else arg]))))))
       `(,new-prim ,@new-args)]
      [`(,func ,args ...)
       (when (equal? counter on-which)
         (return (expand-s grammar token-map 'APP depth)))
        (define new-func
          (match func
            [(? fun?)
             (cond
               [(equal? (+ 1 counter) on-which)
                (expand-s grammar token-map 'FUN depth)]
               [(and (< counter on-which)
                     (>= (+ (count-ast func) counter) on-which))
                (helper func (add1 counter))]
               [else func])]
            [(? expr?)
             (cond
               [(equal? (+ 1 counter) on-which)
                (expand-s grammar token-map 'EXPR depth)]
               [(and (< counter on-which)
                     (>= (+ (count-ast func) counter) on-which))
                (helper func (add1 counter))]
               [else func])]))
        (define counter-after-func (+ (count-ast func) counter))
        (define-values (new-counter new-args)
          (for/fold ([nc counter-after-func]
                     [na '()])
                    ([arg (in-list args)])
            (values (+ nc (count-ast arg))
                    (append
                     na
                     (list (cond
                             [(equal? (+ 1 nc) on-which)
                              (expand-s grammar token-map 'EXPR depth)]
                             [(and (< nc on-which)
                                   (>= (+ (count-ast arg) nc) on-which))
                              (helper arg (+ counter (count-ast arg)))]
                             [else arg]))))))
        `(,new-func ,@new-args)])))
  (helper scheme 0))


(define (string->sexpr s)
  (read (open-input-string s)))

(define (list->hash l)
  (for/fold ([res (hash)])
            ([p (in-list l)])
    (hash-set res (car p) (cdr p))))

(define test-grammar
  (read (open-input-file "./scheme-core.grammar")))
(define test-token
  (list->hash (read (open-input-file "./scheme-core.token"))))

(define test-expr
  '(let ((a 1)
         (b (lambda (x) x)))
     (b a)))


(define grammar-file (make-parameter #f))
(define token-map (make-parameter #f))
(define top-rule-name (make-parameter #f))
(define gen-case-num (make-parameter 0))
(define mode (make-parameter 'none ))
(define expr-to-mutate (make-parameter '()))

(define cmd
  (command-line
   #:usage-help
   "A core scheme code mutator/generater"
   #:once-each
   [("-G" "--generate")
    "generate scheme expressions based on a give top rule and case number"
    (mode 'generate)]
   [("-M" "--mutate")
    "randomly mutate a given expression"
    (mode 'mutate)]
   [("-g" "--grammar")
    gname
    "grammar file path"
    (grammar-file (read (open-input-file gname)))]
   [("-t" "--token")
    tname
    "token mapping file path"
    (token-map (list->hash (read (open-input-file tname))))]
   [("-r" "--rule")
    erule
    "entrance top rule"
    (top-rule-name (string->symbol erule))]
   [("-n" "--number")
    ncase
    "number of case generated"
    (gen-case-num (string->number ncase))]
   [("-e" "--expression")
    mexpr
    "expression need to be mutated"
    (expr-to-mutate mexpr)]))

;; main
(define main
  (match (mode)
    ['none (void)]
    ['generate
     (map displayln
          (map string->sexpr
               (grammar-fuzz (grammar-file) (token-map) (top-rule-name) (gen-case-num))))]
    ['mutate
     (random-mutate (expr-to-mutate) (grammar-file) (token-map))]))
