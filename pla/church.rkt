;; Yihao Sun (ysun67@syr.edu)
;; 2019 in Syracuse

;; this is my interpretor convert core-Scheme IR to church encoding
;; an implementation depend on Prof Kris Micinski's CIS 700 course
;; node and CMCS430 of UMD

;; NOTE: here just cover core scheme except for pattern match

#lang racket

;; the definition of core-scheme IR
(require "./metacircular.rkt")

;; before we start let's see still use some primitive form racket
(define prims '(+ * add1 cons car cdr null? not))

(define (churchify-prim prim)
  (string->symbol (string-append "church:" (symbol->string prim))))

(define (prim? prim)
  (if (member prim prims) #t #f))

;; let's start from data values!

;; nature number
;; we want somthing like peano arithmetic, basicly we choose a id func
;; to encode "O" and multi id to rep "S", but since we want our number
;; can be "maniputate" so we need to leave an entry point just like we
;; should provide **SCC** and **PRED** point

;; as PA let give zero
(define church:zro
  '(λ (f) (λ (x) x)))

;; succ of a nat
(define (church:scc n)
  (match n
    [`(λ (f) (λ (x) ,f-n)) ; =>
     `(λ (f) (λ (x) (f ,f-n)))]
    ))

(define church:+
  `(λ (n) (λ (m)
     (λ (f) (λ (x)
       (n f) ((m f) x))))))

(define church:-
  `(λ (n) (λ (m)
     (λ (f) (λ (x)
       ((n (m f)) x))))))

;; boolean
;; cause boolean is something used to condition check, we can make it
;; a function can work with ture and false callback, #t just return
;; true callback, and in #f just the other one, like (λ (t f) t/f).
;; but since we are in church, we need to make it currify to :
;; (λ (t) (λ (f) t/f))
(define church:tru
  '(λ (t) (λ (f) t)))

(define church:fls
  '(λ (t) (λ (f) f)))

;; tool function to convert a number in meta language(racket)
;; into churh encoding
(define (churchify-metanat num)
  (match num
    [0 church:zro]
    [n (church:scc (churchify-metanat (- n 1)))]
    ))

;; list
;; the list in church encoding is actually similar to boolean,
;; we can consider car and cdr as two callback function
;; when-cons and when-null
(define church:null
  `(λ (wcons) (λ (wnull) wnull)))

(define (church:cons a b)
  `(λ (wcons) (λ (wnull) (wcons ,a ,b))))

;; now let's dealing with s-expr in core scheme data
(define (churchify expr)
  ;; (displayln expr)
  (match expr
    ;; desuger all muti arguments lambda and no args lambda to
    ;; single arg lambda which can fit λ-calulas def well
    ;; anonymous lambda, we just put a dummy arg _ there, since
    ;; church require all function be curify
    [`(λ () ,e) ;=>
     `(λ (_) ,(churchify e))]
    [`(λ (,arg) ,e) ;=>
     `(λ (,arg) ,(churchify e))]
    [`(λ (,arg . ,res) ,e) ;=>
     `(λ (,arg) ,(churchify `(λ (,res) ,e)))]
    ;; variable
    [(? symbol? var) ;=>
     var]
    ;; condition
    [`(if ,e0 ,e1 ,e2) ;=>
     `((,(churchify e0) (λ (_) ,(churchify e1))) (λ (_) ,(churchify e2)))]
    ;; just desugar or/and to if
    [`(and ,e0 ,e1) ;=>
     (churchify `(if ,e0 (if ,e1 #f) #f))]
    [`(or ,e0 ,e1) ;=>
     (churchify `(if ,e0 #t ,e1))]
    ;; datum
    [(? number? nat) ;=>
     (churchify-metanat nat)]
    ;; the arith
    [`(+ ,n0 ,n2) ;=>
     `((,church:+ ,(churchify n0)) ,(churchify n2))]
    [#t ;=>
     church:tru]
    [#f ;=>
     church:fls]
    ;; list
    ['()
     church:null]
    [`(cons ,a ,b)
     (church:cons (churchify a) (churchify b))]
    ;; untagged operations
    ;; procedure in scheme, can just use a id function to close it
    [`(,f) ;=>
     `(,(churchify f) (λ (x) x))]
    [`(,f ,arg) ;=>
     `(,(churchify f) ,(churchify arg))]
    [`(,f ,arg . ,res) ;=>
     (churchify `(,(churchify `(,f ,arg)) ,@res))]
    ))
