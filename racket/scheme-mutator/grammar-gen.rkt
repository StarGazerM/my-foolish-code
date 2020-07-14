;;
;; EBNF style grammar DSL definition in racket
;;
;; Yihao Sun
;; Syracuse 2020

#lang racket

(provide (all-defined-out))

;; ruler is defined by non-term and term node
;; '%NUM and '%SYM are pre-defined term
(define (pattern? p)
  ;; pattern keyword
  (define reserve '(+ * ~ ? or))
  (match p
    ;; 1
    [(? symbol? sym) (not (member sym reserve))]
    ;; optional
    [`(or ,(? pattern?) ,(? pattern?)) #t]
    [`(? ,(? symbol?)) #t]
    ;; 0 or more
    [`(* ,(? pattern?)) #t]
    ;; 1 or more
    [`(+ ,(? pattern?)) #t]
    ;; not something
    [`(~  ,(? symbol?) ...) #t]
    ;; grammar rule
    [(? (listof pattern?)) #t]
    [else #f]))
(define (grammar? g)
  (match g
    [`(term
       ,(? (listof symbol?) terms)
       nonterm
       ((,(? symbol? nonterms) ,(? pattern?)) ...))
     #t]
    [else #f]))

;; is rule 'r' a term/nonterm in grammar 'g'?
(define (term? g r)
  (define prim-term '(%SYM %NUM))
  (match g
    [`(term ,ts nonterm ((,nts ,nt-rules) ...))
     (or (member r prim-term) (member r ts))]))

(define (nonterm? g r)
  (match g
    [`(term ,ts nonterm ((,nts ,nt-rules) ...))
     (member r nts)]))

;; get a rule named 'r' in grammar 'g'
(define (get-rule g r)
  (match g
    [`(term ,ts nonterm ((,nts ,nt-rules) ...))
     (if (member r nts)
         (let/ec return
           (foldl (λ (nt nt-rule res)
                    (if (equal? nt r)
                        (return nt-rule)
                        res))
                  #f nts nt-rules))
         (error (format "~a is not a none terminate rule!" r)))]))

(define (sym-in-pattern pattern)
  (match pattern
    [(? symbol? sym) sym]
    [`(or ,ps ...) (append-map (λ (p) (sym-in-pattern p)) ps)]
    [`(? ,pat) (sym-in-pattern pat)]
    [`(+ ,pat) (sym-in-pattern pat)]
    [`(* ,pat) (sym-in-pattern pat)]
    [`(~ ,sym ...) '()]
    [`(,subs ...) (append-map (λ (sub) (sym-in-pattern sub)) subs)]))


(define (all-node-name g)
  (match g
    [`(term
       ,(? (listof symbol?) terms)
       nonterm
       ((,(? symbol? nonterms) ,(? pattern?)) ...))
     (append terms nonterms)]))

