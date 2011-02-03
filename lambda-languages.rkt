#lang racket

;; Jose Falcon
;; Updated: 2011/01/28

(provide (all-defined-out))

(require redex)

;; lambda calculus extended with natural numbers and a successor function.
(define-language lambda-nat
  (t x
     v
     (t t)
     (add1 t))
  ((w x y z) variable-not-otherwise-mentioned)
  ((n m) natural)
  (v n
     (lambda (x) t)))

;; metafunction for set difference.
(define-metafunction lambda-nat
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x ... y z ...) (y w ...))
   (diff (x ... z ...) (y w ...))
   (side-condition (not (memq (term y) (term (x ...)))))]
  [(diff (x ...) (y z ...)) (diff (x ...) (z ...))])

;; metafunction for set union.
(define-metafunction lambda-nat
  union : (x ...) (x ...) -> (x ...)
  [(union (x ...) ()) (x ...)]
  [(union (x ... y z ...) (y w ...)) (union (x ... y z ...) (w ...))]
  [(union (x ... ) (y z ...)) (union (x ... y) (z ...))])