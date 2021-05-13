#lang racket

(require cKanren/miniKanren)
(require cKanren/neq)
(require cKanren/tree-unify)
(require cKanren/attributes)


;; using list implement a directed graph
;; if a list has an transitive relation pair like ('(1 2) (2 3)) then
;; it is a directed graph

;; from node ... to node ... is a edge with weight ... in graph ...
(define edgeₒ
  (λ (from to weight g)
    (fresh (item to-w w-nil)
      (membero item g)
      (conso from to-w item)
      (conso to w-nil)
      (conso weight '() w-nil))))

;; from node ... to node ... is a path has weight in graph ...
(define pathₒ
  (λ (from to weight g)
    (fresh (mid w1 w2)
      (edgeₒ from mid w1 g)
      (edgeₒ mid to w2 g)
      (number weight)
      (number w1)
      (number w2)
      (== weight (+ w1 w2)))))

(run* (from to weight)
  (pathₒ
   from
   to
   weight
   '((a b 1)
     (b c 2)
     (c d 3))))
