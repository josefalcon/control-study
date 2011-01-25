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
  lambda-shift/reset-abstract
  ;; terms
  (--> t
       (t empty halt dot)
       init)
  
  ;; machine states
  (--> (m e c d)
       (c m d)
       num)
  (--> (x e c d)
       (c lookup(x, e) d)
       var)
  (--> ((lambda (x) t) e c d)
       (c (x t e) d)
       closure)
  (--> ((t_0 t_1) e c d)
       (t_0 e (arg t_1 e c) d)
       app)
  (--> ((succ t) e c d)
       (t e (succ c) d)
       succ)
  (--> ((reset t) e c d)
       (t e halt (d c))
       reset)
  (--> ((shift t) e c d)
       (t extend(e) halt d)
       shift)
  
  ;; continuations
  (--> (halt v d)
       (d v))
  (--> ((arg t e c) v d)
       (t e (fun v c) d))
  (--> ((succ c) m d)
       (c add1(m) d))
  (--> ((fun (x t e) c) v d)
       (t extend(e v) c d))
  (--> ((fun c_1 c_2) v d)
       (c_1 v (d c_2)))
  
  ;; meta-continuations
  (--> ((d c) v)
       (c v d))
  (--> (dot v)
       v))
