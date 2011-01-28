#lang racket

;; Jose Falcon
;; 2011/01/28

(require redex)

;; lambda calculus extended with numbers, succ and shift/reset. this language
;; is a bit difficult to use since we don't have built in recursion
(define-language lambda-shift/reset
  (t m
     x
     (lambda (x) t)
     (t t)
     (add1 t)
     (reset t)
     (shift x t))
  ((x y z) variable-not-otherwise-mentioned)
  (m natural))

;; extended language with environments, continuations, meta-continuations,
;; closures, values and machine states
(define-extended-language lambda-shift/reset-abstract
  lambda-shift/reset
  (e ((x v) ...))
  (c halt
     (arg (t e) c)
     (add1 c)
     (fun v c))
  (d dot
     (d c))
  (v m (x t e) c))

(define lambda-shift/reset-reduction
  (reduction-relation
   lambda-shift/reset-abstract   
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
        (t_0 e (arg (t_1 e) c) d)
        e-app)
   (--> ((add1 t) e c d)
        (t e (add1 c) d)
        e-add1)
   (--> ((reset t) e c d)
        (t e halt (d c))
        e-reset)
   (--> ((shift x_1 t) ((x v) ...) c d)
        (t ((x_1 c) (x v) ...) halt d)
        e-shift)
   ;; continuations
   (--> (halt v d)
        (d v)
        c-halt)
   (--> ((arg (t e) c) v d)
        (t e (fun v c) d)
        c-arg)
   (--> ((add1 c) m d)
        (c ,(add1 (term m)) d)
        c-add1)
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

;; eval-shift/reset-cek : t -> any
;; return a value if the term converges.
(define (eval-shift/reset-cek t)
  (let ([v (apply-reduction-relation* lambda-shift/reset-reduction
                                      (term (,t () halt dot)))])
    (match v
      [`((dot ,(? number? n))) n]
      [`((dot (,x ,t ,e))) 'function]
      [`((dot ,c)) 'continuation]
      [_ 'stuck])))

;; random testing against racket

;; a name space for evaluating Racket programs
(define racket-ns
  (parameterize ([current-namespace (make-base-empty-namespace)])
    (namespace-require 'racket)
    (namespace-require 'racket/control)
    (current-namespace)))

;; eval-shift/reset-racket : t -> any
;; evaluate a lambda-shift/reset program in racket
(define (eval-shift/reset-racket t)
  (define raw-result
    (with-handlers ((exn:fail? (lambda (x) 'stuck)))
      (eval t racket-ns)))
  (cond
    [(procedure? raw-result) 'function]
    [(continuation? raw-result) 'continuation]
    [else raw-result]))

;; equiv-reduction? : t -> boolean
;; determine if cek reduction is equivalent to racket reduction
(define (equiv-reduction? t)
  (let ([cek (eval-shift/reset-cek t)]
        [rack (eval-shift/reset-racket t)])
    (eqv? cek rack)))

;; free-variables
;; determine the free variables in a given term.
(define-metafunction lambda-shift/reset
  free-variables : t -> (x ...)
  [(free-variables m) ()]
  [(free-variables x) (x)]
  [(free-variables (lambda (x) t)) (diff (free-variables t) (x))]
  [(free-variables (t_0 t_1)) (union (free-variables t_0) (free-variables t_1))]
  [(free-variables (add1 t)) (free-variables t)]
  [(free-variables (reset t)) (free-variables t)]
  [(free-variables (shift x t)) (diff (free-variables t) (x))])

;; diff
;; set difference.
(define-metafunction lambda-shift/reset
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x ... y z ...) (y y_1 ...))
   (diff (x ... z ...) (y y_1 ...))
   (side-condition (not (memq (term y) (term (x ...)))))]
  [(diff (x ...) (y z ...)) (diff (x ...) (z ...))])

;; union
;; set union.
(define-metafunction lambda-shift/reset
  union : (x ...) (x ...) -> (x ...)
  [(union (x ...) ()) (x ...)]
  [(union (x ... y z ...) (y y_1 ...)) (union (x ... y z ...) (y_1 ...))]
  [(union (x ... ) (y z ...)) (union (x ... y) (z ...))])

;; close-term
;; close the given free variables of the given term.
(define-metafunction lambda-shift/reset
  close-term : t (x ...) -> t
  [(close-term m (x ...)) m]
  [(close-term y (x ... y z ...)) (lambda (y) y)]
  [(close-term y (x ...)) y]
  [(close-term (lambda (x) t) (y ...)) (lambda (x) (close-term t (y ...)))]
  [(close-term (t_0 t_1) (x ...)) ((close-term t_0 (x ...)) (close-term t_1 (x ...)))]
  [(close-term (add1 t) (x ...)) (add1 (close-term t (x ...)))]
  [(close-term (reset t) (x ...)) (reset (close-term t (x ...)))]
  [(close-term (shift x t) (y ...)) (shift x (close-term t (y ...)))])

;; random testing - this is broken on (term (shift k k)) - no fix yet!
(redex-check
  lambda-shift/reset
  t
  (equiv-reduction? (term t))
  #:prepare (lambda (x) (term (close-term ,x (free-variables ,x)))))