#lang racket

(require redex/reduction-semantics)
(provide (all-defined-out))

(define Church-class
  (term (class Church extends Object
          ([Variable x]
           [Variable f]
           [Variable m]
           [Variable n]
           [Variable g]
           [Variable h]
           [Variable u]
           
           [Abstraction zero]
           [Abstraction one]
           [Abstraction two]
           [Abstraction plus]
           [Abstraction succ]
           [Abstraction mult]
           [Abstraction exp])
          
          ((Church construct()
                   (begin
                     (this $ x := (new Variable))
                     (this $ f := (new Variable))
                     #;(this $ m := (new Variable))
                     (this $ n := (new Variable))
                     #;(this $ g := (new Variable))
                     #;(this $ h := (new Variable))
                     #;(this $ u := (new Variable))
                     
                     (this $ zero := ((new Abstraction) @ construct-x-t ((this $ f)
                                                                         ((new Abstraction) @ construct-x-t ((this $ x) (this $ x))))))
                     
                     (this $ succ := ((new Abstraction) 
                                      @ construct-x-t ((this $ n) 
                                                       ((new Abstraction) 
                                                        @ construct-x-t ((this $ f) 
                                                                         ((new Abstraction) 
                                                                          @ construct-x-t ((this $ x) 
                                                                                           ((new Application) 
                                                                                            @ construct ((this $ f) 
                                                                                                         ((new Application) 
                                                                                                          @ construct (((new Application) 
                                                                                                                        @ construct ((this $ n) 
                                                                                                                                     (this $ f))) 
                                                                                                                       (this $ x))))))))))))
                     #;(this $ plus := ((new Abstraction) 
                                      @ construct-x-t ((this $ m) 
                                                       ((new Abstraction) 
                                                        @ construct-x-t ((this $ n) 
                                                                         ((new Abstraction) 
                                                                          @ construct-x-t ((this $ f) 
                                                                                           ((new Abstraction) 
                                                                                            @ construct-x-t ((this $ x) 
                                                                                                             ((new Application) 
                                                                                                              @ construct (((new Application) 
                                                                                                                            @ construct ((this $ m)
                                                                                                                                         (this $ f))) 
                                                                                                                           ((new Application) 
                                                                                                                            @ construct
                                                                                                                            (((new Application) 
                                                                                                                              @ construct ((this $ n)
                                                                                                                                           (this $ f)))
                                                                                                                             (this $ x))))))))))))))
                     #;(this $ mult := ((new Abstraction)
                                      @ construct-x-t ((this $ m)
                                                       ((new Abstraction)
                                                       @ construct-x-t ((this $ n)
                                                                        ((new Abstraction)
                                                                        @ construct-x-t ((this $ f) 
                                                                                         ((new Abstraction)
                                                                                         @ construct-x-t ((this $ x)
                                                                                                          ((new Application)
                                                                                                          @ construct (((new Application)
                                                                                                                        @ construct ((this $ m)
                                                                                                                                     ((new Application)
                                                                                                                                      @ construct ((this $ n)
                                                                                                                                                   (this $ f)))))
                                                                                                                       (this $ x))))))))))))
			            	            
                     #;(this $ exp := ((new Abstraction) 
                                     @ construct-x-t ((this $ m) 
                                                      ((new Abstraction) 
                                                       @ construct-x-t ((this $ n) 
                                                                        ((new Application) 
                                                                         @ construct ((this $ n) 
                                                                                      (this $ m))))))))
                     
                     (this $ one := ((new Application)
                                     @ construct ((this $ succ) (this $ zero))))
                    
                     #;(this $ one := ((new Abstraction) 
                                     @ construct-x-t ((this $ f)
                                                      ((new Abstraction) 
                                                       @ construct-x-t ((this $ x)
                                                                        ((new Application)
                                                                         @ construct((this $ f)
                                                                                     (this $ x))))))))
                     this
                     ))
           
           (Abstraction zero ()
                        (this $ zero))
           
           (Abstraction one () 
                        (this $ one))
           
           #;(LambdaTerm plus ([LambdaTerm m] [LambdaTerm n])
                       ((new Application)
                        @ construct (((new Application)
                                      @ construct ((this $ plus) m))
                                     n)))
	
           #;(LambdaTerm succ ([LambdaTerm n])
                       ((new Application)
                        @ construct ((this $ succ) n)))
           
           #;(LambdaTerm mult ([LambdaTerm m] [LambdaTerm n])
                       ((new Application)
                        @ construct (((new Application)
                                      @ construct ((this $ mult) m))
                                     n)))
	
           #;(LambdaTerm exp ([LambdaTerm m] [LambdaTerm n])
                       ((new Application)
                        @ construct (((new Application)
                                      @ construct ((this $ exp) m))
                                     n)))
	
           #;(LambdaTerm pred ([LambdaTerm n])
                       ((new Application)
                        @ construct ((this $ pred) n)))

           #;(LambdaTerm minus ([LambdaTerm m] [LambdaTerm n])
                       ((new Application)
                        @ construct (((new Application)
                                      @ construct ((this $ minus) m))
                                     n)))
           
           )
          )
        
        ))

