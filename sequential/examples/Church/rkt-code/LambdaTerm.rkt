#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

(define LambdaTerm-class
  (term (class LambdaTerm extends Object
          () ; list of fields
          () ; list of methods --> it only had abstract methods defined
          )))

