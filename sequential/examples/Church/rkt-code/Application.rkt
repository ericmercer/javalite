#lang racket

(require redex/reduction-semantics)

(provide (all-defined-out))

(define Application-class
  (term (class Application extends LambdaTerm
          ([LambdaTerm t]
           [LambdaTerm s])
          
          ((Application construct ([LambdaTerm t] [LambdaTerm s])
                        (begin (this $ t := t ) 
                               (this $ s := s) 
                               this))
           
           (LambdaTerm cas ([Variable x] [LambdaTerm r])
                       (var LambdaTerm lop := null in
                            (var LambdaTerm rop := null in
                                 (var LambdaTerm v := null in
                                      (begin
                                        (lop := ((this $ t) @ cas (x r)))
                                        (rop := ((this $ s) @ cas (x r)))
                                        (v := ((new Application) @ construct (lop rop)))
                                        v)))))
           
           (bool isFree ([Variable x])
                 (var bool v := ((this $ t) @ isFree(x)) in  
                      (begin 
                        (if ((this $ s) @ isFree(x))
                            (v := true)
                            else
                            unit)
                        v)))
           
           (LambdaTerm ar ([Variable oldVar] [Variable newVar])
                       ((new Application) @ construct (
                                                       ((this $ t) @ ar(oldVar newVar))
                                                       ((this $ s) @ ar(oldVar newVar))
                                                       )
                                          ))
           
           (bool isAe ([LambdaTerm x])
                 (var bool v := false in
                      (begin  
                        (if (x instanceof Application)
                            (var Application a := (Application x) in
                                 (v := (if ((this $ t) @ isAe ((a $ t)))
                                           ((this $ s) @ isAe ((a $ s)))
                                           else
                                           false)))
                            else
                            unit)
                        v)))
           
           (LambdaTerm eval ()
                       (var LambdaTerm lop := ((this $ t) @ eval ()) in
                            (var LambdaTerm rop := ((this $ s) @ eval ()) in
                                 (var LambdaTerm v := null in
                                      (begin
                                        (if (lop instanceof Abstraction)
                                            (var Abstraction a := (Abstraction lop) in
                                                 (v := ((a @ br (rop)) @ eval ())))
                                            else
                                            (v := ((new Application) @ construct (lop rop))))
                                        v)))))
           
           ))))
