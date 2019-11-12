#lang racket

(require racket/control)

;; monadic perform Maybe chain
(define do-tag (make-continuation-prompt-tag 'do))

;; a monad-like adt is a algebra contian
;; it's just Monad like because no real type class here
;; return :: a -> M a
;; bind :: M a -> (a -> M b) -> M b
;; fail :: String -> M a
(define (do-block thnk freturn fbind ffail)
  (let/ec return-do-main
    (letrec ([do-helper
              (λ (pthnk calculated)
                (define next (call/prompt pthnk do-tag))
                (match next
                  ;; continuation execute rest of stack
                  ;; >>
                  [(? continuation?)
                   (do-helper (λ () (next calculated))
                              calculated)]
                  ;; >>=
                  [`(bind ,(? continuation? next-c) ,v)
                   (do-helper (λ () (fbind v next-c))
                              v)]
                  [`(return ,(? continuation? next-c) ,v)
                   ;; things in (next-c lambda) is a side effect
                   ;; for example IO
                   (do-helper (λ () (next-c v))
                              (freturn v))]
                  ;; give up stack when fail
                  ['fail
                   (return-do-main (ffail calculated))]
                  ;; default value case, return it
                  [else calculated]
                  ))])
      (do-helper thnk 'empty))))

;; s :: string
(define (fail s)
  (call/comp
   (λ (ccc)
     (abort/cc do-tag (λ () 'fail)))
   do-tag))

;; v :: a
(define (return v)
  (call/comp
   (λ (ccc)
     (abort/cc do-tag (λ () `(return ,ccc ,v))))
   do-tag))

;; ⟵ can be witted by define
;; cause this is syntax sugar, so just use
;; x :: a
;; m :: M a
(define-syntax-rule (⟵ x m)
    (define x (>>= m)))

;; bind is something  a repackage function, the data type in whole
;; monad may change, so many be a value/type guard needed
;; in do block each 'line' will cause a bind call
;; f :: a -> b
(define (>>= v)
  (call/cc
   (λ (ccc)
     ;; abort/cc is used to replace function call with
     ;; wrapper continuation
     `(bind ,ccc ,v)
     #;(abort/cc do-tag (λ () `(bind ,ccc ,v))))
   do-tag))

;; define maybe
(define (maybe? m)
  (match m
    ['Nothing #t]
    [`(Just ,x) #t]
    [else #f]))

;; def of maybe monad
(define (maybe-return v)
  `(Just ,v))

(define (maybe-fail v)
  'Nothing)

(define (maybe-bind m f)
  (match m
    ['Nothing 'Nothing]
    [`(Just ,x) (f x)]))

;; test
(do-block
 (λ ()
   (⟵ a '(Just 2))
   (>>= '(Just 1))
   (⟵ b '(Just 4))
   (>>= '(Just 2))
   ;; (>>= 'Nothing)
   (>>= `(Just ,(+ a b)))
   )
 maybe-return
 maybe-bind
 maybe-fail)
