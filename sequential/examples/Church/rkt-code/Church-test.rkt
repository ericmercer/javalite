#lang racket

(require racket/sandbox
         redex/reduction-semantics
         "LambdaTerm.rkt"
         "Abstraction.rkt"
         "Application.rkt"
         "Variable.rkt"
         "Function.rkt"
         "SetIfNotZero.rkt"
         "Church.rkt"
         "ChurchTest.rkt")

(provide (all-defined-out))

(define μ-Church
  (term (,LambdaTerm-class
         ,Application-class
         ,Variable-class
         ,Abstraction-class
         ,Function-class
         ,SetIfNotZero-class
         ,Church-class
         ,ChurchTest-class)))

(define (check-syntax CL? μ?)
  (begin
    (test-predicate CL? LambdaTerm-class)
    (test-predicate CL? Application-class)
    (test-predicate CL? Variable-class)
    (test-predicate CL? Abstraction-class)
    (test-predicate CL? Function-class)
    (test-predicate CL? SetIfNotZero-class)
    (test-predicate CL? Church-class)
    (test-predicate CL? ChurchTest-class)
    (test-predicate μ? μ-Church)))
