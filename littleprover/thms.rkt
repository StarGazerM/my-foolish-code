;; Load the J-Bob language:
(include-book "j-bob-lang" :dir :teachpacks)
;; Load J-Bob, our little proof assistant:
(include-book "j-bob" :dir :teachpacks)
;; Load the transcript of all proofs in the book:
(include-book "little-prover" :dir :teachpacks)
;; Run every proof in the book, up to and including the proof of align/align:
(dethm.align/align)

(dethm euqal-same (x)
      (equal (equal x x) 't))

(dethm equal-swap ( x y)
      (equal (equal x y) (equal y x)))

