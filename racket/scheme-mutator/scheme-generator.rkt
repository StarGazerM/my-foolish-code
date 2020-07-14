;;
;; Genrate program based on grammar defined by sexpr-style EBNF specification
;;
;; mostly based on idea here
;; https://www.fuzzingbook.org/html/Grammars.html
;;
;; Yihao Sun
;; 2020 Syracuse

#lang racket

(require "grammar-gen.rkt")

(provide grammar-fuzz
         tokens->sexpr
         expand-g)

;; the cost of a expansion in the sum of all symbol's cost
;; cost to expand a symbol is defined by "cost of expansion in it's max cost expansion"
;; recursive define, so here is base case
;; "the cost of term is one"
;; "if a non-term cause circle in expansion, it's cost is ∞"
;; clearly if all expansion of symbol is ∞, this grammar is wrong
;; since we are going to express more powerfull grammar(ebnf style) we also need to calculate pattern
;; cost. Main reason for cost in my code is just to **minimum** expand program, so I treat * as 0 time
;; and + as 1 time expand
(define (symbol-cost g sym [seen (set)])
  (cond
    [(term? g sym) 1]
    [(set-member? seen sym) +inf.0]
    [(nonterm? g sym)
     (define rule (get-rule g sym))
     (pattern-cost g rule (set-add seen sym))]
    [else (error (format "~a is not a valid rule" sym))]))

(define (pattern-cost g pattern [seen (set)])
  ;;(displayln pattern)
  ;; (displayln (format "~a has appeared before" (set->list seen)))
  (match pattern
    [`(or ,pats ...) (apply min (map (λ (pat) (pattern-cost g pat seen)) pats))]
    [(? symbol? sym) (symbol-cost g sym seen)]
    [`(? ,pat) 0]
    [`(+ ,pat) (pattern-cost g pat seen)]
    [`(* ,pat) 0]
    [`(~ ,sym ...) 1]
    ;; add1 is because each level will have a expansion cost
    [`(,pats ...) (add1 (apply + (map (λ (p) (pattern-cost g p seen)) pats)))]))


(define name-pool '(a b c d aa bb cc dd))
(define REPEAT_RATIO 0.2)

(define (list-at l n)
  (if (<= n 0)
      (car l)
      (car (drop l n))))

;; a 2 flavor expander turn a rule placeholder into a a AST (sexpr style)
;; my fuzzer is much more easier than the one in fuzzer book, in book it will first maximun expand
;; term until it reach some number of nonterminal symbol, then random expand to some max level, finaly
;; expand using minimum expand
;; depth means how many naive expand will be made, if depth is reached, it will try minimum expand
;; if expand a term, generate that term
(define (expand-g g top depth)
  ;;(displayln top)
  (define (rule-cost< rule1 rule2)
    (< (pattern-cost g rule1) (pattern-cost g rule2)))
  ;; we always expand a symbol into a AST
  ;; expand a symbol?, since in real program 2 var name or others maybe can appear
  ;; so sometimes we can generate symbol from existing pool!
  (define (expand-sym sym)
    (define roll (random 0 10))
    (cond
      [(> roll (* REPEAT_RATIO 10)) (gensym)]
      [else (list-at name-pool (random 0 (length name-pool)))]))
  ;; expand a term
  (define (expand-term t)
    (match t
      ['%NUM (random 0 10)]
      ['%SYM (expand-sym t)]
      #;['%BOOL
       (define coin (random 0 2))
       (if (equal? coin 0) #t #f)]
      ;; a real term symbol
      [else t]))
  ;; pure random expand, this will return 
  (define (random-expand g rule)
    (match rule
      [(? symbol? sym)
       (cond
         ;; leave term here, all term will be expanded in minimum expand
         [(term? g sym) sym]
         [(nonterm? g sym) (get-rule g sym)]
         [else (error (format "~a is not a valid grammar rule" sym))])]
      [`(or ,pats ...)
       (define pos (random 0 (length pats)))
       (list-at pats pos)]
      [`(+ ,pat)
       (define counter (random 1 5))
       (define (helper c res)
         (cond
           [(<= c 0) res]
           [else
            (define gen (random-expand g pat))
            (helper (sub1 c) (cons gen res))]))
       (helper counter '())]
      [`(* ,pat)
       (define counter (random 0 5))
       (define (helper c res)
         (cond
           [(<= c 0) res]
           [else
            (define gen (random-expand g pat))
            (helper (sub1 c) (append res (list gen)))]))
       (helper counter '())]
      [`(? ,pat)
       (define coin (random 0 2))
       (if (equal? coin 0)
           '()
           (random-expand g pat))]
      [`(,pats ...)
       (for/fold ([res '()])
                 ([pat (in-list pats)])
         (let ([gen (random-expand g pat)])
           (append res (list gen))
           #;(match pat
             [`(* ,_) (append res gen)]
             [`(+ ,_) (append res gen)]
             [`(,(? pattern?) ...) (append res gen)]
             [else (append res (list gen))])))]))
  ;; minium expansion to get a minimun AST
  (define (minimum-cost-expand g pattern [seen (set)])
    ;;(displayln (format "minimun expand ~a" g))
    (match pattern
      [(? symbol? sym)
        (cond
          [(term? g sym) (expand-term sym)]
          [(nonterm? g sym) (minimum-cost-expand g (get-rule g sym) (set-add seen sym))]
          [else (error (format "~a is not a valid term" sym))])]
      [`(or ,pats ...)
       ;;(displayln (map (λ (p) (pattern-cost g p)) pats))
       (define mini-rule (car (sort pats rule-cost<)))
       (if (equal? (pattern-cost g mini-rule) +inf.0)
           (error "the grammar contain infinity loop!")
           (minimum-cost-expand g mini-rule seen))]
      [`(+ ,pat) (minimum-cost-expand g pat seen)]
      [`(* ,pat) '()]
      [`(~ ,sym ...) (gensym sym)]
      [`(,pats ...)
       (for/fold ([res '()])
                 ([pat (in-list pats)])
         (let ([gen (minimum-cost-expand g pat seen)])
           (append res (list gen))
           #;(match pat
             [`(* ,_) res]
             [`(,(? pattern?) ...) (append res gen)]
             [else (append res (list gen))])))]))
  (flatten
   (cond
     [(< depth 1)
      ;;(displayln (format "before minimum expand expr is ~a" top))
      (minimum-cost-expand g top)]
     [else
      (define ast (random-expand g top))
      (expand-g g ast (sub1 depth))])))


;; this will replace token with real string
(define (tokens->sexpr token-list token-map)
  (define token-str (format "~a" token-list))
  (for/fold ([res ""])
            ([token (in-list token-list)])
    (string-append res (hash-ref token-map token (format "~a" token)) " ")))


;; a naive grammar fuzzer
(define (grammar-fuzz g token-map top case-num)
  (define (helper g top case-num res)
    (if (> case-num 0)
        (let* ([new-case (expand-g g top (random 10 20))]
               [new-case-str (tokens->sexpr new-case token-map)])
          (helper g top (sub1 case-num) (cons new-case-str res)))
        res))
  (helper g top case-num '()))


(define (string->sexpr s)
  (read (open-input-string s)))


(define (list->hash l)
  (for/fold ([res (hash)])
            ([p (in-list l)])
    (hash-set res (car p) (cdr p))))
