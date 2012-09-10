#lang racket

(require racket/sandbox
         redex/reduction-semantics
         "Swap.rkt"
         "SwapTest.rkt")

(provide (all-defined-out))

(define μ-Swap
  (term (,Swap-class
         ,SwapTest-class
         )))

(define (check-syntax CL? μ?)
  (begin
    (test-predicate CL? Swap-class)
    (test-predicate CL? SwapTest-class)
    ))
