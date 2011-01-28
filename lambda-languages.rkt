#lang racket

;; Jose Falcon
;; Updated: 2011/01/28

(provide lambda-nat)

(require redex)

;; lambda calculus extended with natural numbers and a successor function.
(define-language lambda-nat
  (t m
     x
     (lambda (x) t)
     (t t)
     (add1 t))
  ((x y z) variable-not-otherwise-mentioned)
  (m natural))