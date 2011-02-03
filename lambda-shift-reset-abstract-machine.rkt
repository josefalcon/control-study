#lang racket

;; Jose Falcon
;; Updated: 2011/01/28

(require redex)
(require rackunit)
(require "lambda-languages.rkt")

(provide eval-shift/reset-cek)

;; Based on
;; "An Operational Foundation for Delimited Continuations in the CPS Hierarchy".
;; Biernacka, Biernacki, Danvy
;; Logical Methods in Computer Science, 2005

(define-extended-language lambda-shift/reset-abstract
  lambda-shift/reset-base
  (v n (x t e) c)
  (e ((x v) ...))
  (c mt-c
     (arg-c (t e) c)
     (fun-c v c)
     (add-c c))
  (k mt-k
     (k c)))

(define lambda-shift/reset-machine
  (reduction-relation
   lambda-shift/reset-abstract   
   ;; machine states
   (--> (n e c k)
        (c n k)
        e-num)
   (--> (x ((x_0 v_0) ... (x v) (x_1 v_1) ...) c k)
        (c v k)
        e-var
        (side-condition (not (member (term x) (term (x_0 ...))))))
   (--> ((lambda (x) t) e c k)
        (c (x t e) k)
        e-abs)
   (--> ((t_0 t_1) e c k)
        (t_0 e (arg-c (t_1 e) c) k)
        e-app)
   (--> ((add1 t) e c k)
        (t e (add-c c) k)
        e-add1)
   (--> ((reset t) e c k)
        (t e mt-c (k c))
        e-reset)
   (--> ((shift x_1 t) ((x v) ...) c k)
        (t ((x_1 c) (x v) ...) mt-c k)
        e-shift)
   ;; continuations
   (--> (mt-c v k)
        (k v)
        c-mt)
   (--> ((arg-c (t e) c) v k)
        (t e (fun-c v c) k)
        c-arg)
   (--> ((add-c c) n k)
        (c ,(add1 (term n)) k)
        c-add1)
   (--> ((fun-c (x t ((x_1 v_1) ...)) c) v k)
        (t ((x v) (x_1 v_1) ...) c k)
        c-abs)
   (--> ((fun-c c_1 c_2) v k)
        (c_1 v (k c_2))
        c-cntx)
   ;; meta-continuations
   (--> ((k c) v)
        (c v k)
        m-cntxt)))

;; eval-shift/reset-cek : t -> any
;; return a value if the term converges.
(define (eval-shift/reset-cek t)
  (let ([v (apply-reduction-relation* lambda-shift/reset-machine
                                      (term (,t () mt-c mt-k)))])
    (match v
      [`((mt-k ,(? number? n))) n]
      [`((mt-k (,x ,t ,e))) 'function]
      [`((mt-k ,c)) 'function] ; racket represents shift continuations as procedures
      [_ 'stuck])))