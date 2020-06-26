;;
;; Grammar Fuzzer can genrate program based on grammar defined by sexpr-style EBNF specification
;;
;; mostly based on idea here
;; https://www.fuzzingbook.org/html/Grammars.html
;;
;; Yihao Sun
;; 2020 Syracuse

#lang racket


;; ruler is defined by non-term and term node
;; '%NUM and '%SYM are pre-defined term
(define (grammar? g)
  (define (pattern? p)
    (match p
      ;; 1
      [(? symbol?) #t]
      ;; 0 or more
      [`(,(? symbol?) *) #t]
      ;; 1 or more
      [`(,(? symbol?) +) #t]
      [else #f]))
  (match g
    [`(term
       ,(? (listof symbol?) terms)
       nonterm
       (,(? symbol? nonterms) (,(? (listof pattern?) ruless) ...)) ...)
     (define all-left (append terms nonterms '(%NUM %SYM)))
     (and
      (empty? (set-intersect terms nonterms))
      (andmap (λ (rules)
                (andmap (λ (rule)
                          (andmap (λ (p)
                                    (match p
                                      [(? symbol?) (member p all-left)]
                                      [`(,x ,_) (member x all-left)]))
                                  rule))
                        rules))
              ruless))]
    [else #f]))

;; is rule 'r' a term/nonterm in grammar 'g'?
(define/contract (term? g r)
  (-> grammar? symbol? boolean?)
  (match g
    ['%SYM #t]
    ['%NUM #t]
    [`(term ,ts nonterm (,nts ,nt-rules) ...)
     (member r ts)]))

(define/contract (nonterm? g r)
  (-> grammar? symbol? boolean?)
  (match g
    [`(term ,ts nonterm (,nts ,nt-rules) ...)
     (member r nts)]))

;; get a rule named 'r' in grammar 'g'
(define (get-rule g r)
  (match g
    [`(term ,ts nonterm (,nts ,nt-rules) ...)
     (if (member r nts)
         (let/ec return
           (foldl (λ (nt nt-rule res)
                    (if (equal? nt r)
                        (return nt-rule)
                        res))
                  #f nts nt-rules))
         (error (format "~a is not a none terminate rule!" r)))]))

(define (sym-in-rule rule)
  (map (λ (pattern)
         (match pattern
           [(? symbol? sym) sym]
           [`(,sym +) sym]
           [`(,sym *) sym]))
       rule))

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
  (define rules (get-rule g sym))
  (cond
    [(term? g sym) 1]
    [(set-member? seen sym) +inf.0]
    [(nonterm? g sym)
     (apply max (map (λ (rule)
                       (rule-cost g rule (set-add seen sym)))
                     rules))]
    [else (error (format "~a is not a valid rule" sym))]))

(define (pattern-cost g pattern [seen (set)])
  (match pattern
    [(? symbol? sym) (symbol-cost g sym (set-add seen sym))]
    [`(,sym +) (symbol-cost g sym (set-add seen sym))]
    [`(,sym *) 0]))

(define (rule-cost g rule [seen (set)])
  (apply + (map (λ (p) (pattern-cost g p seen)) rule)))

;; compare the cost of rule
(define (rule-cost< rule1 rule2)
  (< (rule-cost rule1) (rule-cost rule2)))

(define name-pool '(a b c d aa bb cc dd))
(define REPEAT_RATIO 0.2)

;; a 2 flavor expander turn a rule placeholder into a a AST (sexpr style)
;; my fuzzer is much more easier than the one in fuzzer book, in book it will first maximun expand
;; term until it reach some number of nonterminal symbol, then random expand to some max level, finaly
;; expand using minimum expand
;; depth means how many naive expand will be made, if depth is reached, it will try minimum expand
;; if expand a term, generate that term
(define (expand-g g top depth)
  ;; we always expand a symbol into a AST
  ;; expand a symbol?, since in real program 2 var name or others maybe can appear
  ;; so sometimes we can generate symbol from existing pool!
  (define (expand-sym sym)
    (define roll (random 0 10))
    (cond
      [(> roll (* REPEAT_RATIO 10)) (gensym)]
      [else (take name-pool (random 0 (length name-pool)))]))
  ;; expand a term
  (define (expand-term t)
    (match t
      ['%NUM (random 0 10)]
      ['%SYM (expand-sym t)]
      ;; a real term symbol
      [else t]))
  ;; pure random expand
  (define (random-expand g sym)
    (cond
      [(term? g sym) (expand-term sym)]
      [(nonterm? g sym)
       (define rules (get-rule g sym))
       (take rules (random 0 (length rules)))]
      [else (error (format "~a is not a valid grammar rule"))]))
  ;; minium expansion to get a minimun AST
  (define (minimun-cost-expand g sym)
    (match sym
      [(? term?) (expand-term sym)]
      [(? nonterm?)
       (define rules (get-rule g sym))
       (define min-cost-rule (first (sort rules rule-cost<)))
       (foldl (λ (pattern res)
                (match pattern
                  [(? symbol? sym) (append res (list (minimun-cost-expand g sym)))]
                  [`(,sym +) (append res (list (minimun-cost-expand g sym)))]
                  [`(,sym *) res]))
              '()
              min-cost-rule)]))
  (cond
    [(< depth 1) (minimun-cost-expand g top)]
    [else
     (define ast (random-expand g top))
     (map (λ (sub)
            (match sub
              [(? term? t) (expand-term t)]
              [(? nonterm? nt) (expand-g g nt (sub1 depth))]
              [else sub]))
          ast)]))

;; a naive grammar fuzzer
(define (grammar-fuzz g seed case-num)
  (define (helper g seed case-num res)
    (define new-case (expand-g g seed (random 1 6)))
    (helper g seed (sub1 case-num) (cons new-case res)))
  (helper g seed case-num '()))
