#lang racket

(provide (all-defined-out))

(define (anf-convert e)
  (define (normalize-ae e k)
    ...)
  (define (normalize-aes es k)
    ...)
  (define (normalize e k)
    (match e
      [(? number? n) (k n)]
      [(? symbol? x) (k x)]
      [`(lambda (,x) ,e0) (k `(lambda (,x) ,(anf-convert e0)))]
      [`(if ,e0 ,e1 ,e2)
       (normalize-ae e0
                     (lambda (ae)
                       (k `(if ,ae ,(anf-convert e1) ,(anf-convert e2)))))]
      [`(,es ...)
       (normalize-aes es k)]))
  (normalize e (lambda (x) x)))

; Flanagan, et al, 1993 (Essence of compiling with continuations)
(define (anf-convert e)
  (define (normalize-ae e k)
    (normalize e (lambda (anf)
                   (match anf
                     [(? number? n) (k n)]
                     [(? symbol? x)
                      (k x)]
                     [`(lambda ,xs ,e0)
                      (k `(lambda ,xs ,e0))]
                     [else
                      (define ax (gensym 'a))
                      `(let ([,ax ,anf])
                         ,(k ax))]))))
  (define (normalize-aes es k)
    (if (null? es)
        (k '())
        (normalize-ae (car es) (lambda (ae)
                                 (normalize-aes (cdr es)
                                                (lambda (aes)
                                                  (k `(,ae ,@aes))))))))
  (define (normalize e k)
    (match e
      [(? number? n) (k n)]
      [(? symbol? x) (k x)]
      [`(lambda (,x) ,e0) (k `(lambda (,x) ,(anf-convert e0)))]
      [`(if ,e0 ,e1 ,e2)
       (normalize-ae e0 (lambda (ae)
                          (k `(if ,ae ,(anf-convert e1) ,(anf-convert e2)))))]
      [`(,es ...)
       (normalize-aes es k)]))
  (normalize e (lambda (x) x)))
