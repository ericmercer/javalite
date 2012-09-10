#lang racket

(require redex/reduction-semantics)

(provide (all-defined-out))

(define Abstraction-class
  (term (class Abstraction extends LambdaTerm
          ([LambdaTerm t]
           [Variable x]
           [Function f])
          (
           (Abstraction construct-x-t([Variable x] [LambdaTerm t])
                        (begin
                          (this $ t := t)
                          (this $ x := x)
                          (this $ f := null)
                          this))
           
           (Abstraction construct-x-f([Variable x] [Function f])
                        (begin
                          (this $ t := x)
                          (this $ x := x)
                          (this $ f := f)
                          this))
           
           (Abstraction construct-x-t-f([Variable x] [LambdaTerm t] [Function f])
                        (begin
                          (this $ t := t)
                          (this $ x := x)
                          (this $ f := f)
                          this))
           
           (LambdaTerm cas ([Variable x] [LambdaTerm r])
                       (var LamdaTerm v := null in
                            (var Variable y := (this $ x) in
                                 (var Variable z := null in
                                      (begin 
                                        (if (x == y) 
                                            (v := this)
                                            else 
                                            (if 
                                             ((r @ isFree (y)) == false)
                                             (v := ((new Abstraction) @ construct-x-t-f (y ((this $ t) @ cas (x r)) (this $ f))))
                                             else 
                                             (begin
                                               (z := (new Variable))
                                               (v := ((new Abstraction) @ construct-x-t-f (z (((this $ t) @ ar (y z)) @ cas (x r)) (this $ f)))))))
                                        v)))))
           
           (bool isFree ([Variable x])
                 (var bool v := false in 
                      (begin 
                        (if ((x == (this $ x)) == false) 
                            (if (((this $ t) @ isFree (x)) == true) 
                                (v := true)
                                else 
                                (v := false))
                            else
                            (v := false))
                        v)))
           
           (LambdaTerm br([LambdaTerm s])
                       (var LambdaTerm v := ((this $ t) @ cas ((this $ x) s)) in
                            (begin
                              (if (((this $ f) == null) == false)
                                  ((this $ f) @ eval ())
                                  else
                                  unit)
                              v)))
           
           (LambdaTerm ar-abstraction([Variable x])
                       (var Variable y := (this $ x) in
                            ((new Abstraction) @ construct-x-t-f (x ((this $ t) @ ar(y x)) (this $ f)))))
           
           (LambdaTerm ar([Variable oldVar] [Variable newVar])
                         (var LambdaTerm v := null in 
                              (var Variable y := (this $ x) in
                                   (var Variable z := null in     
                                        (begin
                                          (if (y == oldVar)
                                              (v := this)
                                              else
                                              (if (y == newVar)
                                                  (begin
                                                    (z := (new Variable))
                                                    (v := ((this @ ar-abstraction (z)) @ ar (oldVar newVar))))
                                                  else
                                                  (v := ((new Abstraction) @ construct-x-t-f ((this $ x) 
                                                                                              ((this $ t) @ ar (oldVar newVar)) 
                                                                                              (this $ f))))))
                                        v)))))
          
          (bool isAe ([LambdaTerm x])
                (var bool v := false in
                     (var Abstraction a := null in
                          (begin
                            (if (x instanceof Abstraction)
                                (begin
                                  (a := (Abstraction x))
                                  (if (((this $ x) @ isAe ((a $ x))) == false)
                                      (a := (Abstraction (a @ ar-abstraction ((this $ x)))))
                                      else
                                      unit)
                                  (v := ((this $ t) @ isAe ((a $ t)))))
                                else
                                unit)
                            v))))
          
          (LambdaTerm eval ()
                      this)
          
          ))))

