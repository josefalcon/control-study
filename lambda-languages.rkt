#lang racket

;; Jose Falcon
;; Updated: 2011/02/02

(require redex)
(provide (all-defined-out))

;;;;;;;;
;; the lambda calculus extended with numbers and successor.
;;;;;;;;

(define-language lambda-base
  (t x
     n
     λ
     (t t)
     (add1 t))
  ((w x y z) variable-not-otherwise-mentioned)
  ((n m) natural)
  (λ (lambda (x) t))
  (v n
     λ))

;; diff
;; set difference for determining free variables
(define-metafunction lambda-base
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x ... y z ...) (y w ...))
   (diff (x ... z ...) (y w ...))
   (side-condition (not (memq (term y) (term (x ...)))))]
  [(diff (x ...) (y z ...)) (diff (x ...) (z ...))])

;; union
;; set union for determining free variables
(define-metafunction lambda-base
  union : (x ...) (x ...) -> (x ...)
  [(union (x ...) ()) (x ...)]
  [(union (x ... y z ...) (y w ...)) (union (x ... y z ...) (w ...))]
  [(union (x ... ) (y z ...)) (union (x ... y) (z ...))])

;; subst
;; variable substitution
(define-metafunction lambda-base
  subst : x any any -> any
  [(subst x any x) any]
  [(subst x any y) y]
  [(subst x any m) m]
  [(subst x any (lambda (x) t)) (lambda (x) t)]
  [(subst x any (lambda (y) t))
   (lambda (w) (subst x any (subst y w t)))
   (where w ,(variable-not-in (term (x any t)) (term y)))]
  [(subst x any (t_1 t_2)) ((subst x any t_1) (subst x any t_2))]
  [(subst x any (add1 t)) (add1 (subst x any t))])

;; free-variables
;; determine the free variables in a given term.
(define-metafunction lambda-base
  free-variables : t -> (x ...)
  [(free-variables n) ()]
  [(free-variables x) (x)]
  [(free-variables (lambda (x) t)) (diff (free-variables t) (x))]
  [(free-variables (t_0 t_1)) (union (free-variables t_0) (free-variables t_1))]
  [(free-variables (add1 t)) (free-variables t)])

;; close-term
;; close the given variables of the given term.
(define-metafunction lambda-base
  close-term : t (x ...) -> t
  [(close-term n (x ...)) n]
  [(close-term y (x ... y z ...)) (lambda (y) y)]
  [(close-term y (x ...)) y]
  [(close-term (lambda (x) t) (y ...)) (lambda (x) (close-term t (y ...)))]
  [(close-term (t_0 t_1) (x ...)) ((close-term t_0 (x ...)) (close-term t_1 (x ...)))]
  [(close-term (add1 t) (x ...)) (add1 (close-term t (x ...)))])

;;;;;;;;
;; the lambda calculus extended with delimited control
;;;;;;;;

(define-extended-language lambda-shift/reset-base lambda-base
  (t ....
     (reset t)
     (shift x t)))

(define-metafunction/extension subst lambda-shift/reset-base
  subst-shift/reset : x any any -> any
  [(subst-shift/reset x any (reset t)) (reset (subst-shift/reset x any t))]
  [(subst-shift/reset x any (shift x t)) (shift x t)]
  [(subst-shift/reset x any (shift y t))
   (shift w (subst-shift/reset x any (subst-shift/reset y w t)))
   (where w ,(variable-not-in (term (x any t)) (term y)))])

(define-metafunction/extension free-variables lambda-shift/reset-base
  free-variables-shift/reset : t -> (x ...)
  [(free-variables-shift/reset (reset t)) (free-variables-shift/reset t)]
  [(free-variables-shift/reset (shift x t))
   (diff (free-variables-shift/reset t) (x))])

(define-metafunction/extension close-term lambda-shift/reset-base
  close-term-shift/reset : t (x ...) -> t
  [(close-term-shift/reset (reset t) (x ...))
   (reset (close-term-shift/reset t (x ...)))]
  [(close-term-shift/reset (shift x t) (y ...))
   (shift x (close-term-shift/reset t (y ...)))])