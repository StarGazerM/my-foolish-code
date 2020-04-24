;; some prototype for nano pass compilation tool
;; for racket s-expression like IR

;; Yihao Sun <ysun67@syr.edu>
#lang racket

(require (for-syntax racket/syntax
                     racket/list
                     racket/pretty))


;; define ir should produce a ir with ir?
(define-syntax (define-ir stx)
  (syntax-case stx ()
    [(define-ir ir-name
       (Term (metas tspecs) ...)
       ((Expr enames patss) ...))
     ;; using some mutable here, should be careful
     (let* ([meta-map (make-hash)]
            [meta-list (syntax->list #'(metas ...))]
            [_ (foldl (λ (m p res)
                        (hash-set! meta-map (syntax->datum m) p))
                      (hash)
                      (syntax->list #'(metas ...))
                      (syntax->list #'(tspecs ...)))])
       (letrec ([replace-meta
                 (λ (stx-p env)
                   (cond
                     [(identifier? stx-p)
                      (define stx-p-data (syntax->datum stx-p))
                      (if (hash-has-key? env stx-p-data)
                          #`,(? #,(hash-ref env stx-p-data))
                          stx-p)]
                     [else
                      (define stx-l (syntax->list stx-p))
                      (datum->syntax stx-p (map (λ (s) (replace-meta s env)) stx-l))]))])
         (with-syntax ([ir-pname (format-id #'ir-name "~a?" #'ir-name)]
                       [ir-vname (generate-temporary 'ir)]
                       [term-pred-name (format-id #'ir-name "~a-term?" #'ir-name)])
           #`(begin
               ;; {ir-name}-term?
               (define (term-pred-name t-reserved)
                 (match t-reserved
                   ((? tspecs metas) #t) ...
                   (else #f)))
               ;; {ename}?
               #,@(for/list ([ename (syntax->list #'(enames ...))]
                             [pats (syntax->list #'(patss ...))])
                    (with-syntax ([ename-pred (format-id ename "~a?" ename)]
                                  [c-tmp (generate-temporary (syntax->datum ename))])
                      #`(define (ename-pred c-tmp)
                          (match c-tmp
                            #,@(for/list ([p (syntax->list pats)])
                                 (cond
                                   [(identifier? p)
                                    (with-syntax ([p-pred
                                                   (hash-ref meta-map (syntax->datum p))])
                                      #`((? p-pred) #t))]
                                   [else
                                    ;; allow recursive
                                    (hash-set! meta-map
                                               (syntax->datum ename)
                                               (syntax->datum #'ename-pred))
                                    #`[`#,(replace-meta p meta-map) #t]]))
                            [else #f]))))
               ;; {ir-name}?
               (define (ir-pname ir-vname)
                 (match ir-vname
                   #,@(for/list ([ename (syntax->list #'(enames ...))])
                        (let ([ename-p (format-id ename "~a?" ename)])
                          #`[(? #,ename-p) #t]))
                   [else #f]))))))]))

;; test
(define-ir lambda-anf
  (Term (x symbol?)
        (num number?)
        (bool boolean?))
  ((Expr aexp
         (x
          num
          bool
          (lambda (x) x)))
   (Expr cexp
         (aexp
          (aexp aexp)
          (let ([x aexp])
            cexp)))))


