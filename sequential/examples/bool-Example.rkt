(require redex/reduction-semantics
         "../util.rkt"
         "../javalite.rkt"
         "../javalite-gc.rkt")
(define boolean-sat-CL
  (term ((class Main extends Object
           () ; no fields
           ((bool testMethod()
                 (begin true))))
         (class bool-op extends Object
           () 
           ((bool and-op((bool v1) (bool v2)) 
                  (var bool result := false in
                       (begin (if (v1 == true) 
                                  (begin (if (v2 == true) true
                                             else false))
                               else false))))
            (bool or-op ((bool v1) (bool v2)) 
                  (var bool result := false in 
                  (begin (if (v1 == true) true else 
                             (begin (if (v2 == true) true 
                                        else false))))))
            (bool not-op ((bool v1))
                  (begin (if (v1 == false) true else false)))
            ))
         (class bool-state extends Object
           ((bool b_v))
           ((bool set_var()
                  (begin true)))
         )
         (class bool-exp extends Object
           ((bool-state v1) (bool-op op) (bool-state v2))
           ((bool set_var()
                  (begin true)))
           )
         (class bool-op extends Object
           () ()
           )
         (class and-bool-op extends bool-op
           () ()
           )
         (class or-bool-op extends bool-op
           () ()
           )
         (class not-bool-op extends bool-op
           () ()
           )
        )))

(define boolean-sat
  (term (,boolean-sat-CL  
         (Main testMethod))))

(test-predicate (redex-match lang P) boolean-sat)
