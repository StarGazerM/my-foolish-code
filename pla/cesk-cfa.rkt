;; Yihao Sun <ysun67@syr.edu>
;; 2019 Syracuse

;; implement a 0-cfa using AAM way

;; this will be performed on a ANF version lambda calculus with if branch
;; syntax
(define (aexp? e)
  (match e
    [(? symbol?) #t]
    [`(λ (,(? symbol?)) ,body) #t]))
