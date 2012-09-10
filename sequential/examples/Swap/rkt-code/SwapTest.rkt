#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

(define SwapTest-class
  (term (class SwapTest extends Object
          ([Swap instance])
          (
           (SwapTest construct ()
                       (var Swap v := ((new Swap) @ construct ()) in 
                            (begin 
                              (this $ instance := v)
                              this)))
           
           (bool testSwap ()
                (var Swap c := (this $ instance) in
                     (begin 
                       (c @ swap ())
                       (if (c $ bFalse)
                           (if (c $ bTrue)
                               false
                               else
                               true)
                           else
                           false))
                       ))
           )
          )))
