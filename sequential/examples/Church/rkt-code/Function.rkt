#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

(define Function-class
  (term (class Function extends Object
          () ; list of fields
          () ; list of methods --> it only had abstract methods defined
          )))
