;; Load the J-Bob language:
(load "j-bob-lang.scm")
;; Load J-Bob, our little proof assistant:
(load "j-bob.scm")
;; Load the transcript of all proofs in the book:
(load "little-prover.scm")
;; Run every proof in the book, up to and including the proof of align/align:
(dethm.align/align)