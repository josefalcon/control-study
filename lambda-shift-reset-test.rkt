#lang racket

(require redex)
(require rackunit)
(require "lambda-languages.rkt")
(require "lambda-shift-reset-abstract-machine.rkt")
(require "lambda-shift-reset-reduction-semantics.rkt")

;;;;;;;;
;; random testing against racket
;;;;;;;;

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
    #;[(continuation? raw-result) 'function]
    [else raw-result]))

;; equiv-reduction? : t -> boolean
;; determine if cek reduction is equivalent to racket reduction
(define (equiv-reduction? t)
  (let ([cek (eval-shift/reset-cek t)]
        [red (eval-shift/reset-red t)]
        [rack (eval-shift/reset-racket t)])
    (pretty-print t)
    (andmap (lambda (x) (eqv? red x)) (list cek rack))))

;; prepare-term : t -> t
;; close the free variables in a term
(define (prepare-term t)
  (term (reset
         (close-term-shift/reset
          ,t
          (free-variables-shift/reset ,t)))))

(check-true (equiv-reduction? (term (reset (shift m m)))))
(check-true (equiv-reduction? (term (reset (shift e (add1 (shift ok e)))))))
(redex-check lambda-shift/reset-base t (equiv-reduction? (term t)) #:prepare prepare-term)