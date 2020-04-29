;; some prototype for nano pass compilation tool
;; for racket s-expression like IR

;; Yihao Sun <ysun67@syr.edu>
#lang racket

(require (for-syntax racket/syntax
                     racket/list
                     racket/pretty
                     racket/match))

;; a symbol-map for extend a language
;; IRStxTable :: {ir-name ↦ (MetaMap :: {name ↦ syntax})}
(define-for-syntax ir-stx-table
  (make-hash))

;; check if something is defined
(define-for-syntax (defined? stx)
  (syntax-case stx ()
    [(_ id)
     (with-syntax ([v (identifier-binding #'id)])
       #''v)]))

;; define ir should produce a ir with ir?
(define-syntax (define-ir stx)
  ;; the symbol to mark `Modified`
  (define (mod-symbol? m) (member m '(M ✎)))
  ;; replace syntax by refering a `env` map
  (define (replace-meta stx-p env)
    (cond
      [(identifier? stx-p)
       (define stx-p-data (syntax->datum stx-p))
       (cond
         ;; escape wild card
         [(equal? stx-p-data '_)
          #',_]
         [(hash-has-key? env stx-p-data)
          #`,(? #,(hash-ref env stx-p-data))]
         [else stx-p])]
      [else
       (define stx-l (syntax->list stx-p))
       (datum->syntax stx-p (map (λ (s) (replace-meta s env)) stx-l))]))
  (define replaced-stx
    (syntax-case stx ()
      ;; define a new ir
      [(define-ir ir-name
         (Term (metas tspecs) ...)
         (Production (enames patss) ...))
       ;; using some mutable here, should be careful
       ;; meta map is for extend, pred map is for replacement inside current ir
       (let* ([meta-map (make-hash)]
              [pred-map (make-hash)]
              [meta-list (syntax->list #'(metas ...))]
              [_ (hash-set! ir-stx-table (syntax->datum #'ir-name) meta-map)]
              [_ (foldl (λ (m p res)
                          (hash-set! pred-map (syntax->datum m) p)
                          (hash-set! meta-map (syntax->datum m) p))
                        (hash)
                        (syntax->list #'(metas ...))
                        (syntax->list #'(tspecs ...)))])
         (with-syntax ([ir-pname (format-id #'ir-name "~a?" #'ir-name)]
                       [ir-vname (generate-temporary 'ir)]
                       [t-reserved (generate-temporary)]
                       [term-pred-name (format-id #'ir-name "~a-term?" #'ir-name)])
           #`(begin
               ;; {ir-name}-term?
               (define (term-pred-name t-reserved)
                 (match t-reserved
                   [(? tspecs metas) #t] ...
                   (else #f)))
               ;; {ir-name}-{meta}?
               ;; term here is mainly for extend
               #,@(for/list ([meta (syntax->list #'(metas ...))]
                             [tspec (syntax->list #'(tspecs ...))])
                    (with-syntax ([meta-pred-name (format-id meta "~a-~a?" #'ir-name meta)])
                      #`(define meta-pred-name #,tspec)))
               ;; {ir-name}-{ename}?
               #,@(for/list ([ename (syntax->list #'(enames ...))]
                             [pats (syntax->list #'(patss ...))])
                    (with-syntax ([ename-pred (format-id ename "~a-~a?" #'ir-name ename)]
                                  [c-tmp (generate-temporary)])
                      #`(define (ename-pred c-tmp)
                          (match c-tmp
                            #,@(begin
                                 (hash-set! pred-map
                                            (syntax->datum ename)
                                            #'ename-pred)
                                 (hash-set! meta-map
                                            (syntax->datum ename)
                                            pats)
                                 (for/list ([p (syntax->list pats)])
                                   (cond
                                     [(identifier? p)
                                      (with-syntax ([p-pred
                                                     (hash-ref pred-map (syntax->datum p))])
                                        #`((? p-pred) #t))]
                                     [else
                                      ;; allow recursive
                                      #`[`#,(replace-meta p pred-map) #t]])))
                            [else #f]))))
               ;; {ir-name}?
               (define (ir-pname ir-vname)
                 (match ir-vname
                   #,@(for/list ([ename (syntax->list #'(enames ...))])
                        (let ([ename-p (format-id ename "~a-~a?" #'ir-name ename)])
                          #`[(? #,ename-p) #t]))
                   [else #f])))))]
      ;; extends a exist ir
      [(define-ir ir-name
         (Extend parent-ir)
         (Term
          tchanges ...)
         (Production
          (mods enames echangess) ...))
       (unless (hash-has-key? ir-stx-table (syntax->datum #'parent-ir))
         (raise-syntax-error
          (syntax-e #'Extend)
          (format "parent ir \"~a\" is not defined"
                  (syntax->datum #'parent-ir))))
       (let* ([meta-map (hash-copy (hash-ref ir-stx-table (syntax->datum #'parent-ir)))]
              [pred-map (make-hash)]
              [tchange-list (syntax->list #'(tchanges ...))]
              [_ (hash-set! ir-stx-table (syntax->datum #'ir-name) meta-map)]
              [_ (for ([k (hash-keys meta-map)])
                   (define v (hash-ref meta-map k))
                   (cond
                     [(identifier? v)
                      ;; (displayln (format "k: ~a \n v: ~a" k v))
                      (hash-set! pred-map k v)]
                     [else
                      (hash-set! pred-map k
                                 (datum->syntax
                                  v
                                  (format "~a-~a?"
                                          (syntax->datum #'ir-name) k)))]))]
              [_ (map (λ (tc)
                        (match (syntax->list tc)
                          [(list +-s term-added pred-added)
                           #:when (equal? (syntax->datum +-s) '+)
                           (hash-set! pred-map (syntax->datum term-added) pred-added)
                           (hash-set! meta-map (syntax->datum term-added) pred-added)]
                          [(list --s term-removed pred-removed)
                           #:when (equal? (syntax->datum --s) '-)
                           (hash-remove! meta-map (syntax->datum term-removed))]
                          [else (raise-syntax-error
                                 (syntax-e #'Extend)
                                 "can only +/- terminates when extand language terminate symbol")]))
                      tchange-list)])
         (with-syntax ([ir-pname (format-id #'ir-name "~a?" #'ir-name)]
                       [ir-vname (generate-temporary 'ir)]
                       [t-vname (generate-temporary 'term-match)]
                       [parent-p-name (format-id #'parent-ir "~a?" #'parent-ir)]
                       [term-parent-p-name (format-id #'parent-ir "~a-term?" #'parent-ir)]
                       [term-pred-name (format-id #'ir-name "~a-term?" #'ir-name)])
           #`(begin
               ;; {ir-name}-term?
               (define (term-pred-name t-vname)
                 (match t-vname
                   #,@(for/list ([tc tchange-list])
                        (match (syntax->list tc)
                          [(list +-s term-added pred-added)
                           #:when (equal? (syntax->datum +-s) '+)
                           #`[(? #,pred-added) #t]]
                          [(list --s term-removed pred-removed)
                           #:when (equal? (syntax->datum --s) '-)
                           #`[(? #,pred-removed) #f]]))
                   [(? term-parent-p-name) #t]
                   [else #f]))
               ;; {ir-name}-{ename}?
               #,@(begin
                    ;; reconstrunct from parent and update metamap
                    (for ([mod (syntax->datum #'(mods ...))]
                          [ename (syntax->list #'(enames ...))]
                          [echanges (syntax->list #'(echangess ...))])
                      (let ([ename-pred (format-id ename "~a-~a?" #'ir-name ename)])
                        (match mod
                          ['+
                           (hash-set! pred-map (syntax->datum ename) ename-pred)
                           (hash-set! meta-map (syntax->datum ename) echanges)]
                          ['-
                           (hash-remove! meta-map (syntax->datum ename))]
                          [(? mod-symbol?)
                           (hash-set! pred-map (syntax->datum ename) ename-pred)
                           (define parent-rules (syntax->list (hash-ref meta-map (syntax->datum ename))))
                           (define after-mod
                             (for/fold ([res parent-rules])
                                       ([echange (syntax->list echanges)])
                               (match (syntax->list echange)
                                 [(list mod-r rule)
                                  #:when (equal? (syntax->datum mod-r) '-)
                                  (filter (λ (x)
                                            (not (equal? (syntax->datum rule)
                                                         (syntax->datum x))))
                                          res)]
                                 [(list mod-r rule)
                                  #:when (equal? (syntax->datum mod-r) '+)
                                  (cons rule res)]
                                 [else
                                  (raise-syntax-error
                                   (syntax->datum mod)
                                   "only +, - is allowed when modify an production")])))
                           (hash-set! meta-map (syntax->datum ename) (datum->syntax echanges after-mod))]
                          [else
                           (raise-syntax-error
                            mod
                            "only  +,- or (M/✎) can be used when extend a parent language")])))
                    ;; generate function
                    (for/fold ([res '()])
                              ([mname (hash-keys meta-map)])
                      (define mrule (hash-ref meta-map mname))
                      (with-syntax ([mname-pred (hash-ref pred-map mname)]
                                    [m-tmp (generate-temporary)])
                        (cond
                          [(identifier? mrule)
                           res]
                          [else
                           `(,@res
                             ,#`(define (mname-pred m-tmp)
                                  (match m-tmp
                                    #,@(for/list ([r (syntax->list mrule)])
                                         (cond
                                           [(identifier? r)
                                            #`[(? #,(hash-ref pred-map (syntax->datum r))) #t]]
                                           [else
                                            #`[`#,(replace-meta r pred-map) #t]]))
                                    [else #f])))]))))
               (define (ir-pname ir-vname)
                 (match ir-vname
                   #,@(for/fold ([res '()])
                                ([pname (hash-keys meta-map)])
                        (define p-pred (hash-ref pred-map pname))
                        (cond
                          [(identifier? (hash-ref meta-map pname))
                           res]
                          [else
                           (append res (list #`[(? #,p-pred) #t]))]))
                   [else #f])))))]))
  ;; for debug
  ;;(pretty-display (syntax->datum replaced-stx))
  replaced-stx)


;; test
;; (define-ir anf
;;   (Term (x symbol?)
;;         (num number?))
;;   (Production
;;    (aexp
;;     ;; →
;;     (x
;;      num
;;      (lambda (x ...) _)))
;;    (cexp
;;     ;; →
;;     (aexp
;;      (aexp aexp)
;;      (let ([x aexp] ...)
;;        cexp)))))

;; (define-ir anf/if
;;   (Extend anf)
;;   (Term
;;    (+ bool boolean?))
;;   (Production
;;    (M aexp
;;       ((+ bool)))
;;    (+ if-exp
;;       ((if aexp cexp cexp)))
;;    (M cexp
;;       ((+ if-exp)))))

;; (anf? '(let ([foo 1])
;;          (lambda (y) foo)))

;; (anf/if-if-exp?
;;  '(if #t (lambda (x) x) (lambda (x) x)))

;; (anf/if?
;;  '(let ([b #f])
;;     b))

;; (anf/if?
;;  '(let ([b #f])
;;     ((lambda (x)
;;        (if b 1 2))
;;      (lambda (x) x))))
