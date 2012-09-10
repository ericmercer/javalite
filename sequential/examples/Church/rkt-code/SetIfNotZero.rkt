#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

(define SetIfNotZero-class
  (term (class SetIfNotZero extends Function
          ([Variable x]
           [Variable y]
           [bool bam])
          
          ((Function construct ()
                     (begin
                       (this $ x := (new Variable))
                       (this $ y := (new Variable))
                       (this $ bam := false)
                       this))
           
           (unit eval ()
                 (this $ bam := true))
           
           (unit doEval ([LambdaTerm c])
                 (((new Application) 
                   @ construct (((new Application) 
                                 @ construct (c 
                                              ((new Abstraction) 
                                               @ construct-x-f ((this $ x) this))))
                                ((new Abstraction) 
                                 @ construct-x-t ((this $ y) (this $ y))))) @ eval ())))
          )))
