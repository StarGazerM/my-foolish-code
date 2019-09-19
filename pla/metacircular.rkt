;; CIS 700 -- Metacircular interpreter and Homework 1
;; 
;; Kris Micinski, Fall '19, Syracuse University
#lang racket

(provide (all-defined-out))

;; Definition of core scheme
(define (expr? e)
  (match e
    [(? symbol? var) #t]
    [(? lit?) #t]
    [`(λ (,xs ...) ,body) #t]
    [`(if ,(? expr? guard)
          ,(? expr? etrue)
          ,(? expr? efalse)) #t]
    [`(let* ([,(? symbol? xs) ,(? expr? x-bodies)] ...)
        ,(? expr? body)) #t]
    [`(letrec ([,(? symbol?) (λ (,xs ...) ,(? expr?))] ...)
        ,(? expr? body)) #t]
    [`(,(? builtin?) ,(? expr? args) ...) #t]
    [`(,(? expr? e0) ,(? expr? e1) ...) #t]))

(define (lit? e)
  (match e
    [(? number?) #t]
    [(? string?) #t]
    [(? boolean?) #t]
    [else #f]))

(define (builtin? x)
  (set-member? (set '+ '- '* '/ 'cons 'car 'cdr 'list 'list? '= 'empty? 'number? 'string? 'string-append 'string-length 'length) x))

; Mapping from symbols to the primitive built-in functions within
; Racket.
(define builtins 
  (make-hash (list (cons '+ +)
                   (cons '- -)
                   (cons '* *)
                   (cons '/ /)
                   (cons 'cons cons)
                   (cons 'car car)
                   (cons 'cdr cdr)
                   (cons 'list list)
                   (cons '= equal?)
                   (cons 'empty? empty)
                   (cons 'number? number?)
                   (cons 'string? string?)
                   (cons 'string-append string-append)
                   (cons 'string-length string-length)
                   (cons 'length length)
                   (cons 'or (λ (a b) (or a b)))
                   (cons 'zero? zero?)
                   (cons 'list? list?))))

;; Core-Scheme grammar extended to allow match statements
(define (mexpr? e)
  (match e
    [(? symbol? var) #t]
    [(? lit?) #t]
    [`(λ (,xs ...) ,body) #t]
    [`(if ,(? expr? guard)
          ,(? expr? etrue)
          ,(? expr? efalse)) #t]
    [`(let* ([,(? symbol? xs) ,(? expr? x-bodies)] ...)
        ,(? expr? body)) #t]
    [`(letrec ([,(? symbol?) (λ (,xs ...) ,(? expr?))] ...)
        ,(? expr? body)) #t]
    [`(,(? builtin?) ,(? expr? args) ...) #t]
    [`(,(? expr? e0) ,(? expr? e1) ...) #t]
    [`(match ,(? expr? match-expr)
        [,(? match-pattern? patterns) ,(? expr? bodies)] ...) #t]))

;; Match patterns in *our* language. Note: these are *not* the same as
;; Racket's match patterns. We are implementing a subset of match
;; patterns for our language. If you are confused about this, please
;; make sure you understand this predicate and write out some
;; examples.
(define (match-pattern? mp)
  (match mp
    ;; Something that looks like (? predicate? x) (Note: predicates
    ;; don't have to end w/ ?, but do by convention).
    [`(? ,predicate ,binding-var) #t]
    ;; Matches a cons pattern where the cons matches pattern
    ;; car-pattern, and cdr matches cdr-pattern. For example: (cons (?
    ;; (λ (x) #t) x) (? (λ (x) #t) y)) matches any cons
    ;; pattern. Note that--in our language--the base patern *must* be
    ;; something like (? predicate? x).
    [`(cons ,(? match-pattern? car-pattern) ,(? match-pattern? cdr-pattern)) #t]
    ;; Matches a finite list of elements.
    [`(list ,(? match-pattern? subpatterns) ...) #t]))


;; Interpreter for HW1
(define (interp-hw1 e env)
  ; Might want to turn this on for debugging
  ; (displayln (format "~a ; ~a" e env))
  (match e
    ;; Variable lookup
    [(? symbol? var) (hash-ref env var)]
    ;; Literals
    [(? lit?) e]
    ;; TODO: implement multi-argument λ. Right now this only
    ;; handles single-argument λ (throws away rest of arguments).
    [`(λ (,vars ...) ,body)
     ;; Copy the environment mutably
     (λ args
       (let ([env-copy (make-hash
                        (hash-map env
                                  (λ (x y) (cons x y))))]
             [args-l (if (list? args) args (list args))])
         ;;(hash-set! env-copy (first vars) x)
         (map (λ (k v) (hash-set! env-copy k v)) vars args-l)
         (interp-hw1 body env-copy)))]
    ;; TODO: implement let* correctly
    [`(let* ([,(? symbol? name) ,(? expr? bind-body)] ...)
        ,(? expr? body))
     (let* ([env-copy (make-hash
                      (hash-map env
                                (λ (x y) (cons x y))))]
            [rset (λ (k b s) (hash-set! s k (interp-hw1 b s)))])
       (map (λ (k b) (hash-set! env-copy k (interp-hw1 b env-copy))) name bind-body)
       (interp-hw1 body env-copy))]
    ;; TODO: handle multi-argument letrec (still only one f)
    [`(letrec ([,(? symbol? f) (λ (,f-args ...) ,f-body)])
        ,(? expr? body))
     ;; Make a mutable copy of the hash table
     (let ([env-copy (make-hash
                      (hash-map env
                                (λ (x y) (cons x y))))])
       ;; NOTE: this implementation is *WRONG*. It throws away the
       ;; rest of the arguments past the first...
        (hash-set! env-copy
                  f
                  (λ x (interp-hw1
                               f-body
                               (begin
                                 ;(hash-set! env-copy (first f-args) x)
                                 (map (λ (arg v) (hash-set! env-copy arg v)) f-args x)
                                 env-copy))))
       ;; (map (λ (f)
       ;;     (hash-set! env-copy
       ;;               f
       ;;               (λ (vals) (interp-hw1
       ;;                          f-body
       ;;                          (begin
       ;;                            (map (λ (arg v) (hash-set! env-copy arg v)) f-args vals)
       ;;                            env-copy)))))
       ;;  fs)
       ;; Now interpret the body with this updated (mutable) env
       (interp-hw1 body env-copy))]
    ;; Builtins! (Once you get multi-argument application to work, you
    ;; should be able to delete this branch and the code should work
    ;; the same.)
    [`(,(? builtin? op) ,(? expr? builtin-args) ...)
     ;; Evaluate each argument and then apply the builtin denotation
     ;; of the function.
     (let ([evaluated-args (map (λ (arg) (interp-hw1 arg env)) builtin-args)])
       ;; Take care to undersand this: it is the hint for how to
       ;; understand multi-arg evaluation.
       (apply (hash-ref builtins op) evaluated-args))]
    ;; TODO. Compile a match statement. To implement this you should
    ;; need only to change the implementation of `compile-match-stmts`
    ;; below.
    [`(match ,(? expr? e) [,match-patterns ,match-bodies] ...)
     (eval-match-statements match-patterns match-bodies (interp-hw1 e env) env)]
    ;; If
    [`(if ,(? expr? guard)
          ,(? expr? etrue)
          ,(? expr? efalse)) 
     (if (interp-hw1 guard env)
         (interp-hw1 etrue env)
         (interp-hw1 efalse env))]
    ;; TODO. Application: right now this only handles single-argument
    ;; application (throws away the rest of e-args).
    [`(,(? expr? e0) ,(? expr? e-args) ...)
     ;; ((interp-hw1 e0 env) (interp-hw1 (first e-args) env))]
     (apply (interp-hw1 e0 env) (map (λ (arg) (interp-hw1 arg env)) e-args))]
    ))


;; TODO: extend this function.  Basic idea: translate each match
;; pattern as a λ that returns *either* an updated environment
;; that correctly binds the bodies (if it is successful) or returns
;; #f. Translate each match pattern into this function and then
;; perform application. If this results in #f, move on to try the next
;; match pattern (unless there are none left, in which case throw an
;; error).
(define (eval-match-statements patterns bodies matching-value env)
  ;; Compiles an individual match statement to a λ which will
  ;; return either an updated environment (capturing variables as
  ;; appropriate).
  (define (compile-match-statement pattern env)
    (match pattern
      [`(? ,predicate? ,var)
       (λ (x) (if (begin
                         (hash-set! env var x)
                         ((interp-hw1 predicate? env) x))
                       env
                       #f))]
      [`(cons ,car-pattern ,cdr-pattern)
       (λ (x)
         (if (cons? x)
             (let ([env-after-car ((compile-match-statement car-pattern env) (car x))])
               (if env-after-car
                   ((compile-match-statement cdr-pattern env-after-car) (cdr x))
                   #f))
             #f))]
      ;; Special case to handle matching on the empty list. (A good
      ;; solution in the next part should cover this case!)
      [`(list)
       (λ (x) (and (list? x) (equal? (length x) 0)))]
      ;; TODO. Fill in your answer here. This can nicely be done as
      ;; follows.
      ;;
      ;; HINTS:
      ;; - Create a λ (as in the case of cons) that accepts a list x
      ;;
      ;; - Check immediately whether list? is true of x, and whether
      ;; the length of x is equal to the length of patterns (else this
      ;; can't match).
      ;; 
      ;; - For each index i between 0 <= i < (length patterns), check
      ;; that (compile-match-statement) applies to the pattern at
      ;; index i and ith element of the list x. If it does, return
      ;; that updated environment. You can do this easily using foldl.
      [`(list ,patterns ...)
       (λ (xs)
         (if (and (list? xs)
                 (equal? (length xs) (length patterns)))
            (foldl (λ (p x e)
                     (if e
                        ((compile-match-statement p e) x)
                        #f))
                  env
                  patterns
                  xs)
            #f))]))

  ;; Recursively try each pattern in order until we find one that
  ;; applies. If there are no more patterns, throw an error.
  (define (try-each-pattern patterns bodies matching-value env)
    (if (empty? patterns)
        ;; Error, no patterns left
        (error "No more possible patterns to match")
        ;; Otherwise, compile the first pattern into a λ whose
        ;; job it is it to return either an updated environment (which
        ;; will be used to evaluate the body) or #f (indicating that
        ;; the match failed and we should move on to the next).
        (let* ([compiled-match-statement
                (compile-match-statement (first patterns) env)]
               [updated-env (compiled-match-statement matching-value)])
          (if updated-env 
              (interp-hw1 (car bodies) updated-env)
              (try-each-pattern (cdr patterns) (cdr bodies) matching-value env)))))

  ;; Finally, try each in turn
  (try-each-pattern patterns bodies matching-value env))

