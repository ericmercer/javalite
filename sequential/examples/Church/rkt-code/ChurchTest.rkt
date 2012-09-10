#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

(define ChurchTest-class
  (term (class ChurchTest extends Object
          (
           [Church instance]
           [LambdaTerm three]
           [LambdaTerm two]
           [LambdaTerm five]
           [SetIfNotZero sinz]
           )
          
          (
           
           (bool m ([bool x])
                 x)
           
           (bool n ()
                 true)
                 
           (bool methodInvokeTest ()
                 (this @ m ((this @ n ()))))
           
           (ChurchTest construct ()
                       (var Church v := ((new Church) @ construct ()) in 
                            (begin 
                              (this $ instance := v)
                              #;(this $ two := (v @ plus ((v @ one ()) (v @ one ()))))
                              #;(this $ three := (v @ plus ((v @ one ()) (this $ two))))
                              #;(this $ five := (v @ plus ((this $ three) (this $ two))))
                              (this $ sinz := ((new SetIfNotZero) @ construct ()))
                              this)))
           
           (bool testZeroJavalite ()
                 (var Church c := (this $ instance) in
                      (var SetIfNotZero s := (this $ sinz) in
                           (begin 
                             (s $ bam := false)
                             (s @ doEval ((c @ zero ())))
                             (s $ bam)))))
           
           (bool testNotZeroJavalite ()
                (var Church c := (this $ instance) in
                      (var SetIfNotZero s := (this $ sinz) in
                           (begin 
                             (s $ bam := false)
                             (s @ doEval ((c @ one ())))
                             (s $ bam)))))
           
            (bool testJavaliteVariableEquivalence ()
                  (var Variable x := (new Variable) in 
                       (var Variable y := (new Variable) in
                            (x == y))))   
            
            (bool testJavaliteVariableEquivalence2 ()
                  (var SetIfNotZero x := (new SetIfNotZero) in 
                       (var SetIfNotZero y := (new SetIfNotZero) in
                            (begin 
                              (x $ bam := true)
                              (x == y)))))
           )
          )))
