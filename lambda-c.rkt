#lang racket

;; Jose Falcon
;; Updated: 2011/01/28

(require redex)
(require "lambda-languages.rkt")

;; lambda-nat with A and C operators from Felleisen et al. 1986
(define-extended-language lambda-c lambda-nat
  (t ....
     (abort t)
     (capture t)))

(define-extended-language lambda-c-context lambda-c
  (v n
     (lambda (x) t))
  (E hole
     (E t)
     (v E)
     (add1 E)))

(define lambda-c-reduction
  (reduction-relation
   lambda-c-context
   (--> (in-hole E (add1 n))
        (in-hole E ,(add1 (term n)))
        add)
   (--> (in-hole E ((lambda (x) t) v))
        (in-hole E (subst x v t))
        beta-v)
   (--> (in-hole E (abort v))
        v
        abort)
   (--> (in-hole E (capture (lambda (x) t)))
        ((lambda (x) t) (lambda (y) (in-hole E y)))
        (fresh y)
        capture)))

(define-metafunction lambda-c-context
  subst : x any any -> any
  [(subst x any x) any]
  [(subst x any y) y]
  [(subst x any m) m]
  [(subst x any (lambda (x) t)) (lambda (x) t)]
  [(subst x any (lambda (y) t))
   (lambda (w) (subst x any (subst y w t)))
   (where w ,(variable-not-in (term (x any t)) (term y)))]
  [(subst x any (t_1 t_2)) ((subst x any t_1) (subst x any t_2))]
  [(subst x any (add1 t)) (add1 (subst x any t))]
  [(subst x any (abort t)) (abort (subst x any t))]
  [(subst x any (capture t)) (capture (subst x any t))])