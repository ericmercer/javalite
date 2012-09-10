#lang racket
(require redex/reduction-semantics
         racket/sandbox
         racket/pretty
         "./javalite.rkt"
         "./javalite-gc.rkt"
         "./util.rkt"
         "../examples/Swap/rkt-code/Swap-test.rkt")

(define-syntax (inject-cond stx)
  (syntax-case stx ()
    [(_ prog)
     #'(term (inject prog))]))

(define-syntax (inject/with-state-cond stx)
  (syntax-case stx ()
    [(_ init method)
     #'(term (inject/with-state ,init method))]))

(check-syntax (redex-match javalite CL) (redex-match javalite μ))

#;(define theGC gc)
(define theGC (λ (x) x))

(with-limits 10000 #f
             
             (define init
               (apply-reduction-relation/random
                expr-reductions
                (inject-cond (,μ-Swap (SwapTest construct)))
                theGC #f))
             
             (define testSwap/def
               (inject/with-state-cond init testSwap))
             
             (test-program/true testSwap/def theGC #f))

(test-results)
