#lang racket

;; Jose Falcon
;; Updated: 2011/02/01

(require redex)
(require "lambda-languages.rkt")

;; lambda-nat with shift/reset.
(define-extended-language lambda-shift/reset-base lambda-nat
  (t ....
     (reset t)
     (shift x t)))

;; language extended with values, contexts and meta-contexts.
(define-extended-language lambda-shift/reset lambda-shift/reset-base
  (v .... (hide-hole c))
  (c hole
     (c t)
     (v c)
     (add1 c))
  (k halt
     (k (hide-hole c))))

;; reduction semantics
(define lambda-shift/reset-reduction
  (reduction-relation
   lambda-shift/reset
   #:domain t
   (--> t
        (plug* (k c) ,(add1 (term n)))
        (where ((k c) (add1 n)) (decompose t))
        add1)
   (--> t
        (plug* (k c) (subst x v t_*))
        (where ((k c) ((lambda (x) t_*) v)) (decompose t))
        beta-v)
   (--> t
        (plug* (k hole) (subst x c t_*))
        (where ((k c) (shift x t_*)) (decompose t))
        shift)
   (--> t
        (plug* ((k c) c_1) v)
        (where ((k c) (c_1 v)) (decompose t))
        beta-cntxt)
   (--> t
        (plug* (k c) v)
        (where ((k c) (reset v)) (decompose t))
        reset)))

(define-metafunction lambda-shift/reset
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
  [(subst x any (reset t)) (reset (subst x any t))]
  [(subst x any (shift x t)) (shift x t)]
  [(subst x any (shift y t))
   (shift w (subst x any (subst y w t)))
   (where w ,(variable-not-in (term (x any t)) (term y)))])


(define-metafunction lambda-shift/reset
  decompose : t -> ((k c) t)
  [(decompose t) (decompose* (halt hole) t)])

(define-metafunction lambda-shift/reset
  decompose* : (k c) t -> ((k c) t)
  [(decompose* (k c) (c_1 t)) (decompose* (k (c_1 c)) t)]
  [(decompose* (k c) (t_0 t_1)) (decompose* (k (c t_1)) t_0)]
  [(decompose* (k c) (add1 t)) (decompose* (k (add1 c)) t)]
  [(decompose* (k c) (reset t)) (decompose* ((k c) hole) t)]
  [(decompose* (k (c t)) v) (decompose* (k (v c)) t)]
  [(decompose* (halt hole) v) ((halt hole) v)]
  [(decompose* ((k c) hole) v) ((k c) (reset v))]
  [(decompose* (k c) (shift x t)) ((k c) (shift x t))]
  [(decompose* (k ((lambda (x) t) c)) v) ((k c) ((lambda (x) t) v))]
  [(decompose* (k (c_1 c)) v) ((k c) (c_1 v))]
  [(decompose* (k (add1 c)) n) ((k c) (add1 n))])

(define-metafunction lambda-shift/reset
  plug* : (k c) t -> t
  [(plug* (halt hole) t) t]
  [(plug* ((k c) hole) t) (plug* (k c) (reset t))]
  [(plug* (k (c t_1)) t_0) (plug* (k c) (t_0 t_1))]
  [(plug* (k (v c)) t) (plug* (k c) (v t))]
  [(plug* (k (add1 c)) t) (plug* (k c) (add1 t))])