#lang racket

;; Jose Falcon
;; Updated: 2011/02/02

(require redex)
(require "lambda-languages.rkt")

(provide eval-shift/reset-red)

;; Based on
;; "An Operational Foundation for Delimited Continuations in the CPS Hierarchy".
;; Biernacka, Biernacki, Danvy
;; Logical Methods in Computer Science, 2005

(define-extended-language lambda-shift/reset lambda-shift/reset-base
  (t .... c)
  (v .... c)
  (c mt-c        ;; contexts
     (arg-c t c)
     (fun-c v c)
     (add-c c))
  (k mt-k        ;; meta-contexts
     (k c)))

(define lambda-shift/reset-reduction
  (reduction-relation
   lambda-shift/reset
   #:domain t
   (--> t
        (plug* (k c) ,(add1 (term n)))
        (where ((k c) (add1 n)) (decompose t))
        add1)
   (--> t
        (plug* (k c) (subst-shift/reset x v t_*))
        (where ((k c) ((lambda (x) t_*) v)) (decompose t))
        beta-v)
   (--> t
        (plug* (k mt-c) (subst-shift/reset x c t_*))
        (where ((k c) (shift x t_*)) (decompose t))
        shift)
   (--> t
        (plug* ((k c) c_*) v)
        (where ((k c) (c_* v)) (decompose t))
        beta-cntxt)
   (--> t
        (plug* (k c) v)
        (where ((k c) (reset v)) (decompose t))
        reset)))

(define-metafunction lambda-shift/reset
  decompose : t -> ((k c) t)
  [(decompose t) (decompose* (mt-k mt-c) t)])

(define-metafunction lambda-shift/reset
  decompose* : (k c) t -> ((k c) t)
  [(decompose* (k c) (t_0 t_1)) (decompose* (k (arg-c t_1 c)) t_0)]
  [(decompose* (k c) (add1 t)) (decompose* (k (add-c c)) t)]
  [(decompose* (k c) (reset t)) (decompose* ((k c) mt-c) t)]
  [(decompose* (k (arg-c t c)) v) (decompose* (k (fun-c v c)) t)]
  [(decompose* (mt-k mt-c) v) ((mt-k mt-c) v)]
  [(decompose* ((k c) mt-c) v) ((k c) (reset v))]
  [(decompose* (k c) (shift x t)) ((k c) (shift x t))]
  [(decompose* (k (fun-c (lambda (x) t) c)) v) ((k c) ((lambda (x) t) v))]
  [(decompose* (k (fun-c c_1 c)) v) ((k c) (c_1 v))]
  [(decompose* (k (add-c c)) n) ((k c) (add1 n))]
  [(decompose* (k c) t) ((k c) t)])

(define-metafunction lambda-shift/reset
  plug* : (k c) t -> t
  [(plug* (mt-k mt-c) t) t]
  [(plug* ((k c) mt-c) t) (plug* (k c) (reset t))]
  [(plug* (k (arg-c t_1 c)) t_0) (plug* (k c) (t_0 t_1))]
  [(plug* (k (fun-c v c)) t) (plug* (k c) (v t))]
  [(plug* (k (add-c c)) t) (plug* (k c) (add1 t))])

;; eval-shift/reset-red : t -> any
;; return a value if the term converges.
(define (eval-shift/reset-red t)
  (let ([v (apply-reduction-relation* lambda-shift/reset-reduction (term ,t))])
    (match v
      [`(,(? number? n)) n]
      [`(,(? (redex-match lambda-shift/reset (lambda (x) t)))) 'function]
      [`(,(? (redex-match lambda-shift/reset c))) 'function] ; racket represents shift continuations as procedures
      [_ 'stuck])))