#lang racket

(require redex/reduction-semantics)
(provide (all-defined-out))

(define Swap-class
  (term (class Swap extends Object
          (
           [bool bFalse]
           [bool bTrue]
           )
          
          (
          (Swap construct () (begin
                               (this $ bFalse := false)
                               (this $ bTrue := true)
                               
                               this))
          
          (unit swap () (begin
                          (var bool tmp := (this $ bTrue) in
                               (begin
                                 (this $ bTrue := (this $ bFalse))
                                 (this $ bFalse := tmp)
                                 ))))
          )
          )
))