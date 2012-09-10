#lang racket

(require redex/reduction-semantics)

(provide (all-defined-out))

(define Variable-class
  (term (class Variable extends LambdaTerm
          ([bool fix])
          ((LambdaTerm cas ([Variable x] [LambdaTerm r])
                       (var Variable v := this in 
                            (begin
                              (if (this == x)  
                                  (v := r)
                                  else 
                                  unit)
                              v)))
           
           (bool isFree ([Variable x])
                 (var bool v := false in
                      (begin
                        (if (x == this) 
                            (v := true)
                            else 
                            unit)
                        v)))
           
           (LambdaTerm ar ([Variable oldVar] [Variable newVar])
                       (var LabdaTerm v := this in
                            (begin 
                              (if (oldVar == this) 
                                  (v := newVar)
                                  else 
                                  unit)
                              v)))
           
           (bool isAe ([LambdaTerm x])
                 (x == this))
           
           (LambdaTerm eval () 
		this)
	
           )
          )))


