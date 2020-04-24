;; this a lens util to manipulate a complex list data structure based on predicates
;; not a real lens ~

;; Yihao Sun <ysun67@syr.edu>
;; 2020 Syracuse

#lang racket

;; len into to somewhere nested in a a data
;; take a list based data , a list of predicate to match into this datas a
;; lens-look ::  list? -> (listof (predicate [× procedure?]))
(define (lens-look data pred&filters)
  (define predl (map and/c pred&filters))
  (define (helper d)
    (match d
      ['() '()]
      [`(,hd . ,tl)]))
  (foldl (λ (p res)
           (cons
            (map (λ (in) (lens-looks in ) (filter p data))
            res))
         '()
         predl))
