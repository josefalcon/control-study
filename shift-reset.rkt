#lang racket

(require redex)

;; lambda calculus extended with numbers, succ and shift/reset
(define-language lambda-shift/reset
  (t m
     x
     (lambda (x) t)
     (t t)
     (succ t)
     (reset t)
     (shift (x) t))
  (x variable-not-otherwise-mentioned)
  (m natural))

;; extended language with environments, continuations, meta-continuations,
;; closures and values
(define-extended-language lambda-shift/reset-abstract
  lambda-shift/reset
  (e empty
     ((x v) e))
  (c halt
     (arg (t e) c)
     (succ c)
     (fun v c))
  (d dot
     (d c))
  (v m (x t e) c))

(define lambda-shift/reset-reduction
  (reduction-relation
   lambda-shift/reset-abstract
   ;; terms
   (--> t
        (t empty halt dot)
        init)
   
   ;; machine states
   (--> (m e c d)
        (c m d)
        e-num)
   (--> (x ((x_0 v_0) ... (x v) (x_1 v_1) ...) c d)
        (c v d)
        e-var
        (side-condition (not (member (term x) (term (x_0 ...))))))
   (--> ((lambda (x) t) e c d)
        (c (x t e) d)
        e-abs)
   (--> ((t_0 t_1) e c d)
        (t_0 e (arg t_1 e c) d)
        e-app)
   (--> ((succ t) e c d)
        (t e (succ c) d)
        e-succ)
   (--> ((reset t) e c d)
        (t e halt (d c))
        e-reset)
   (--> ((shift (x_1) t) ((x v) ...) c d)
        (t ((x_1 c) (x v) ...) halt d)
        e-shift)
   
   ;; continuations
   (--> (halt v d)
        (d v)
        c-halt)
   (--> ((arg t e c) v d)
        (t e (fun v c) d)
        c-arg)
   (--> ((succ c) m d)
        (c ,(add1 (term m)) d)
        c-succ)
   (--> ((fun (x t ((x_1 v_1) ...)) c) v d)
        (t ((x v) (x_1 v_1) ...) c d)
        c-abs)
   (--> ((fun c_1 c_2) v d)
        (c_1 v (d c_2))
        c-cntx)
   
   ;; meta-continuations
   (--> ((d c) v)
        (c v d)
        m-cntxt)))
   ;(--> (dot v)
    ;    (v empty halt dot))))
  