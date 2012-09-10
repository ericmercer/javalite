#lang racket
(require redex/reduction-semantics
         "javalite.rkt"
         "javalite-gc.rkt")

(define random-term
  (generate-term javalite P 10))

(define fig1-CL
  (term ((class Main extends Object
           () ; no fields
           ((bool testMethod((Node n) (Node m))
                  (begin 
                     (var bool result := true in
                          (begin (if (n == null)  false 
                                  else
                                  (begin (if (m == null) false
                                          else 
                                          (begin (if (
                                                      begin ((m @ check()) == false)) false
                                                  else 
                                                  (begin 
                                                     (var Node nPrime := null in 
                                                          (begin (n @ swapFirstTwoNodes())))
                                                     (if (m instanceof XNode)
                                                         (begin 
                                                           (var XNode im := null in
                                                                (begin (XNode m)
                                                                       (if (im == nPrime) false 
                                                                           else true)))) 
                                                      else true)))))))
                            )))
                  ))
          )
          (class Node extends Object 
            ((Node next))
            ((bool check () 
                   (begin true))
             (Node swapFirstTwoNodes ()
                   (begin 
                     (var Node result := null in 
                          (begin 
                            (if ((this $ next) == null) 
                                (result := this) else
                                (begin
                                  (var Node t := (this $ next) in (begin
                                                                  (t := (t $ next))
                                                                  (var Node t_next := (t $ next) in (t_next := this))
                                                                  (result := t)))))))))))
          (class XNode extends Node
            ((bool elem))
            ((bool check ()
                   (begin (this $ elem)))))
          (class YNode extends Node
            ()
            ())  
          (class ZNode extends Node
            ()
            ())
          )))

(define fig1
  (term (,fig1-CL  
         (Main testMethod))))

(define church-encoding
  (term (((class number extends Object 
            ()
            ((number zero()
                     (begin 
                       (var number zero := null 
                            (lambda (f)
                              (lambda (zero)
                                zero)))))
             (bool add()
                   (begin true)))
            ))
         (number add)))
  )

(test-predicate (redex-match javalite P) fig1)

; -----------------------------------------------------
; ------------------ REWRITE TESTS --------------------
; -----------------------------------------------------

(define-syntax-rule (test-->* red st mt ...)
  (test-predicate (-test-->* red mt ...) st))

(define ((-test-->* red . mts) st)
  (define not-seen (make-hash))
  (for ([mt (in-list mts)])
    (hash-set! not-seen mt #t))
  (let loop ([t st])
    (hash-remove! not-seen t)
    (or (zero? (hash-count not-seen))
        (let ([ts (apply-reduction-relation red t)])
          (ormap loop ts)))))

(define ex
  (reduction-relation
   javalite
   [--> 1 2] [--> 2 3] [--> 3 4] [--> 4 5] [--> 5 1]))

(test-->* ex 1
          2 4)

; variable access
(local [(define h-simple
          (term (((mt [1 -> null]) 
                 [2 -> (C1 (Object) (C1))])[3 -> (addr 2 C1)])))
        (define η-simple
          (term ((mt [x -> 1]) [y -> 3])))] 
  (test--> expr-reductions
         (term (() ,h-simple ,η-simple x ret))
         (term (() ,h-simple ,η-simple null ret)))
  (test--> expr-reductions
           (term (() ,h-simple ,η-simple y ret))
           (term (() ,h-simple ,η-simple (addr 2 C1) ret))))

;; new
(local [(define μ-test
          (term ((class C0 extends Object ([C0 w] [unit x])()) (class C1 extends C0 ([bool y] [unit z]) ()) )))
        (define tstate
          (term (,μ-test mt mt (new C1) ret)))]
  
  (test-predicate (redex-match javalite μ) μ-test)
  (test-predicate (redex-match javalite state) tstate)
  
  (test--> expr-reductions
           (term (,μ-test mt mt (new C1) ret))
           (term (,μ-test (h-extend* mt [0 -> null] [1 -> unit] [2 -> false] [3 -> unit]
                                     [4 -> (C1 (Object) (C0 (w 0) (x 1)) (C1 (y 2) (z 3)))]) mt 
                          (addr 4 C1) ret))))
      
; field access - object evaluation
(test--> expr-reductions 
         (term (() mt mt (x $ foo) ret))
         (term (() mt mt x (* $ foo -> ret))))

; field access
(local [(define h-test 
          (term (((((mt [1 -> (C2 (Object) (C2))]) [2 -> unit])
                 [3 -> (C1 (Object) (C1 [x 2] [y 4]))])[4 -> (addr 1 C2)])[5 -> (addr 3 C1)])))]
  
  (test--> expr-reductions
           (term (() ,h-test mt (addr 3 C1) (* $ x -> ret)))
           (term (() ,h-test mt unit ret)))
  (test--> expr-reductions
           (term (() ,h-test mt (addr 3 C1) (* $ y -> ret)))
           (term (() ,h-test mt (addr 1 C2) ret)))
  (test-->* expr-reductions
            (term (() ,h-test (mt [x -> 5]) (x $ x) ret))
            (term (() ,h-test (mt [x -> 5]) unit ret))))

; method invocation - object evaluation
(test--> expr-reductions
         (term (() mt mt (e @  m (x y (x == y))) ret))
         (term (() mt mt e (* @ m (x y (x == y)) -> ret))))
(test--> expr-reductions
         (term (() mt mt ((x $ y) @ m (x y (x == y))) ret))
         (term (() mt mt (x $ y) (* @ m (x y (x == y)) -> ret))))

; method invocation - arg0 eval
(test--> expr-reductions
         (term (() mt mt 
                   (addr 1 C1) (* @ m (x y (x $ f)) -> ret)))
         (term (() mt mt 
                   x ((addr 1 C1) @ m () * (y (x $ f)) -> ret))))

; method invocation - argi eval
(test--> expr-reductions
         (term (() mt mt 
                   true ((addr 1 C1) @ who (true false) * (y (x $ f)) -> ret)))
         (term (() mt mt 
                   y ((addr 1 C1) @ who (true false true) * ((x $ f)) -> ret))))

; method invocation - no args
(test--> expr-reductions
         (term (() mt mt (addr 1 C1) (* @ m () -> ret)))
         (term (() mt mt (raw (addr 1 C1) @ m ()) ret)))

; raw method invocation
(local [(define μ-test
          (term ((class C0 extends Object ()((T m ([T x] [T y] [T z]) (begin true)))) (class C1 extends C0 () ()) )))
        (define h-test
          (term (h-extend* mt [0 -> (C0 (Object) (C0))])))
        (define η-test
          (term mt))]
  
  (test-->* expr-reductions
           (term (,μ-test 
                  ,h-test 
                  ,η-test 
                  (raw (addr 0 C0) @ m (true null false)) ret))
           (term (,μ-test 
                  (h-extend* ,h-test [1 -> (addr 0 C0)] [2 -> true] [3 -> null] [4 -> false])         
                  (η-extend* ,η-test [this -> 1] [x -> 2] [y -> 3] [z -> 4])
                  (begin true) 
                  (pop ,η-test ret)))))

; method invocation general
(local [(define μ-test
          (term ((class C0 extends Object ()((T m ([T x] [T y] [T z]) (begin true)))) (class C1 extends C0 () ()) )))
        (define h-test
          (term (h-extend* mt [3 -> (C0 (Object) (C0))] [0 -> true] [1 -> false] [2 -> null] [4 -> (addr 3 C0)])))
        (define η-test
          (term (η-extend* mt [this -> 4] [i -> 0] [j -> 1] [k -> 2])))]
  
  (test-->* expr-reductions
           (term (,μ-test ,h-test ,η-test (this @ m (i j k)) ret))
           (term (,μ-test ,h-test ,η-test this (* @ m (i j k) -> ret)))
           (term (,μ-test ,h-test ,η-test (addr 3 C0) (* @ m (i j k) -> ret)))
           (term (,μ-test ,h-test ,η-test i ((addr 3 C0) @ m () *(j k) -> ret)))
           (term (,μ-test ,h-test ,η-test j ((addr 3 C0) @ m (true) * (k) -> ret)))
           (term (,μ-test ,h-test ,η-test k ((addr 3 C0) @ m (true false) * () -> ret)))
           (term (,μ-test ,h-test ,η-test (raw (addr 3 C0) @ m (true false null)) ret))
           (term (,μ-test 
                  (h-extend* ,h-test [5 -> (addr 3 C0)] [6 -> true] [7 -> false] [8 -> null]) 
                  (η-extend* ,η-test [this -> 5] [x -> 6] [y -> 7] [z -> 8]) 
                  (begin true) (pop ,η-test ret)))))

; equals '=='
(local [(define h-test
          (term (h-extend* mt [0 -> true] [1 -> true] [2 -> false])))
        (define η-test
          (term (η-extend* mt [x -> 0] [y -> 1] [z -> 2])))]
  
  (test-->* expr-reductions
           (term (() ,h-test ,η-test (x == x) ret))
           (term (() ,h-test ,η-test true ret)))
  (test-->* expr-reductions
           (term (() ,h-test ,η-test (y == y) ret))
           (term (() ,h-test ,η-test true ret)))
  (test-->* expr-reductions
           (term (() ,h-test ,η-test (y == z) ret))
           (term (() ,h-test ,η-test false ret))))

; typecast (C e)
(local [(define h-test
          (term (h-extend* mt [0 -> (C1 (Object) (C0) (C1 [f 0]) (C2))] [1 -> (addr 0 C1)])))
        (define η-test
          (term (η-extend* mt [x -> 1])))]
  
  (test-->* expr-reductions
            (term (() ,h-test ,η-test (C2 x) ret))
            (term (() ,h-test ,η-test (addr 0 C2) ret)))
  (test-->* expr-reductions
            (term (() ,h-test ,η-test (Object x) ret))
            (term (() ,h-test ,η-test (addr 0 Object) ret))))

; instanceof  
(test-->* expr-reductions
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) (x instanceof C) ret))
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) x (* instanceof C -> ret)))
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) true ret)))

(test-->* expr-reductions
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) (x instanceof D) ret))
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) x (* instanceof D -> ret)))
          (term (() ((mt [0 -> (C (Object) (C))])[1 -> (addr 0 C)]) (mt [x -> 1]) false ret)))

(test--> expr-reductions
         (term (() (mt (0 -> (C (Object) (C)))) mt (addr 0 C) (* instanceof C -> ret)))
         (term (() (mt [0 -> (C (Object) (C))]) mt true ret)))

(test-predicate (redex-match javalite (μ h η v (* instanceof C -> k))) 
                (term (() (mt (0 -> (C (Object) (C)))) mt (addr 0 C) (* instanceof C -> ret))))

; assign
(test-->* expr-reductions
          (term (() (mt [0 -> true]) (mt [x -> 0]) (x := false) ret))
          (term (() (mt [0 -> true]) (mt [x -> 0]) false (x := * -> ret)))
          (term (() (mt [0 -> false]) (mt [x -> 0]) false ret)))

; field assign
(local [(define h_0
          (term ((((mt [0 -> (C (Object) (C [f 1]))]) [1 -> true]) [2 -> false])[3 -> (addr 0 C)])))]
  
  (test-predicate (redex-match javalite h) h_0)
  (test-term-equal (h-lookup ,h_0 (η-lookup ((mt [x -> 3])[y -> 2]) x))
                   (addr 0 C))
  
  (test-->* expr-reductions
           (term (() ,h_0 ((mt [x -> 3]) [y -> 2]) (x $ f := y) ret))
           (term (() ,h_0 ((mt [x -> 3]) [y -> 2]) false (x $ f := * -> ret)))
           (term (() (h-extend* ,h_0 [1 -> false]) ((mt [x -> 3]) [y -> 2]) false ret))))      

; if-the-else
(test-->* expr-reductions
          (term (() (mt [0 -> true]) (mt [x -> 0]) (if x true else false ) ret))
          (term (() (mt [0 -> true]) (mt [x -> 0]) x (if * true else false -> ret)))
          (term (() (mt [0 -> true]) (mt [x -> 0]) true ret)))

(test-->> expr-reductions
          (term (() (mt [0 -> false]) (mt [x -> 0]) (if x true else false ) ret))
          (term (() (mt [0 -> false]) (mt [x -> 0]) false ret)))

; variable declaration
(test-->* expr-reductions
          (term (() (mt [0 -> null]) (mt [y -> 0]) (var bool x := false in x) ret))
          (term (() (mt [0 -> null]) (mt [y -> 0]) false (var bool x := * in x -> ret)))
          (term (() ((mt [0 -> null]) [1 -> false]) ((mt [x -> 1]) [y -> 0]) x (pop (mt [y -> 0]) ret)))
          (term (() ((mt [0 -> null]) [1 -> false]) ((mt [x -> 1]) [y -> 0]) false (pop (mt [y -> 0]) ret)))
          (term (() ((mt [0 -> null]) [1 -> false]) (mt [y -> 0]) false ret)))

; begin
(test--> expr-reductions
         (term (() mt mt (begin) ret))
         (term (() mt mt unit ret)))

(local [(define h_0
          (term ((((mt [0 -> unit]) [1 -> null]) [2 -> true]) [3 -> false])))
        (define η_0
          (term ((((mt [w -> 0]) [x -> 1]) [y -> 2]) [z -> 3])))]
        
        (test-->* expr-reductions
                  (term (() ,h_0 ,η_0 (begin w x y z) ret))
                  (term (() ,h_0 ,η_0 w (begin * (x y z) -> ret)))
                  (term (() ,h_0 ,η_0 unit (begin * (x y z) -> ret)))
                  (term (() ,h_0 ,η_0 x (begin * (y z) -> ret)))
                  (term (() ,h_0 ,η_0 y (begin * (z) -> ret)))
                  (term (() ,h_0 ,η_0 z (begin * () -> ret)))
                  (term (() ,h_0 ,η_0 false ret))))
         
; pop η
(test--> expr-reductions
         (term (() mt (mt [x -> 2]) true (pop (mt [x -> 3]) ret)))
         (term (() mt (mt [x -> 3]) true ret)))

; -----------------------------------------------------
; -------------- HELPER FUNCTIONS TESTS ---------------
; -----------------------------------------------------
(define-syntax-rule (test-term-equal lhs rhs)
  (test-equal (term lhs) (term rhs)))

(test-predicate (redex-match javalite object) 
                (term (C1 (Object) (C2 [x 0] [y 10] [z 3]))))

; default-value
(test-term-equal (default-value unit) unit)
(test-term-equal (default-value bool) false)
(test-term-equal (default-value C) null)
(test-term-equal (default-value Object) null)

; default-value*
(test-term-equal (default-value* (unit)) (unit))
(test-term-equal (default-value* (bool C unit)) (false null unit))
(test-term-equal (default-value* ()) ())

; h-max
(test-term-equal (h-max mt) -1)
(test-term-equal (h-max (mt [0 -> (C1 (Object) (C2 [x 0] [y 10] [z 3]))])) 0)
(test-term-equal (h-max (mt [3 -> unit])) 3)
(test-term-equal (h-max ((mt [4 -> true]) [3 -> unit])) 4)

; h-malloc
(test-term-equal (h-malloc mt) 0)
(test-term-equal (h-malloc (mt [0 -> true])) 1)
(test-term-equal (h-malloc (mt [3 -> false])) 4)
(test-term-equal (h-malloc ((mt [4 -> true]) 
                            [3 -> (C1 (Object) (C2 [x 0] [y 10] [z 3]))])) 
                 5)

; h-malloc-n
(test-term-equal (h-malloc-n mt 5) (0 1 2 3 4))
(test-term-equal (h-malloc-n (mt [3 -> true]) 1) (4))
(test-term-equal (h-malloc-n (mt [3 -> true]) 0) ())
(test-term-equal (h-malloc-n (mt [3 -> true]) 3) (4 5 6))

; h-malloc-n*
(test-term-equal (h-malloc-n* mt 0 1 2 3) (() (0) (1 2) (3 4 5)))
(test-term-equal (h-malloc-n* mt 2)((0 1)))
(test-term-equal (h-malloc-n* (mt [3 -> true]) 2) ((4 5)))
(test-term-equal (h-malloc-n* (mt [3 -> true]) 2 0 3) ((4 5) () (6 7 8)))

; storelike-lookup
(test-term-equal (storelike-lookup (mt [a -> 1]) a) 1)
(test-term-equal (storelike-lookup ((mt [a -> 1]) [a -> 2]) a) 2)
(test-term-equal (storelike-lookup ((mt [a -> 1]) [b -> 2]) a) 1)

; h-lookup
(test-term-equal (h-lookup (mt [1 -> true]) 1) 
                 true)
(test-term-equal (h-lookup ((mt [1 -> true]) [1 -> true]) 1) 
                 true)
(test-term-equal (h-lookup ((mt [1 -> false]) [2 -> (foo)]) 1) 
                 false)
(test-term-equal (h-lookup ((mt [1 -> (doo (doo [f 0] [y 10] [whoo 3]))]) 
                            [2 -> (foo (foo))]) 1) 
                 (doo (doo [f 0] [y 10] [whoo 3])))

; field lookup
(test-term-equal (field-lookup (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3])) x)
                 3)
(test-term-equal (field-lookup (C1 (Obj) (C1 [x 1] [y 2]) (C2 [x 3])) x)
                 1)
(test-term-equal (field-lookup (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3])) y)
                 2)
(test-term-equal (field-lookup (C2 (Obj) (C1 [y 1] [y 2]) (C2 [x 3])) y)
                 2)

(define μ-simple
  (term ((class C1 extends Object ()((T M1 ([T x] [T y] [T z]) (begin true)))) (class C2 extends C1 () ()) )))

(test-predicate (redex-match javalite μ) μ-simple)

; class-parrents+self
(test-term-equal (class-parents+self ,μ-simple Object)
                 (Object))
(test-term-equal (class-parents+self ,fig1-CL Object)
                 (Object))
(test-term-equal (class-list-extend (Object C1) C2)
                 (Object C1 C2))
(test-term-equal (class-parents+self ,μ-simple C2)
                 (Object C1 C2))
(test-term-equal (class-parents+self ,fig1-CL Node)
                 (Object Node))
(test-term-equal (class-parents+self ,fig1-CL XNode)
                 (Object Node XNode))
(test-term-equal (class-parents+self ,fig1-CL YNode)
                 (Object Node YNode))
(test-term-equal (class-parents+self ,fig1-CL Main)
                 (Object Main))

; fields-list-extend
(test-term-equal (field-lists-extend () ())
                 (()))

; fields-parents+self
(local [(define μ_0
         (term ((class C1 extends Object ([C1 x] [C1 y])()) (class C2 extends C1 ([C1 z]) ()) (class C3 extends C2 () ()))))]
  
  (test-term-equal (fields-parents+self ,μ_0 Object)
                   (()))
  (test-term-equal (fields-parents+self ,μ_0 C1)
                   (() ([C1 x] [C1 y])))
  (test-term-equal (fields-parents+self ,μ_0 C2)
                   (() ([C1 x] [C1 y]) ([C1 z])))
  (test-term-equal (fields-parents+self ,μ_0 C3)
                   (() ([C1 x] [C1 y]) ([C1 z]) ())))
                  
; method-lookcup
(test-term-equal (method-lookup (class-lookup ,μ-simple C1) m)
                 error)
(test-term-equal (method-lookup (class-lookup ,fig1-CL Node) m)
                 error)
(test-term-equal (method-lookup (class-lookup ,fig1-CL Node) check)
                 (Node () (begin true)))
(test-term-equal (method-lookup (class-lookup ,μ-simple C1) M1)
                 (C1 (x y z) (begin true)))
(test-predicate (redex-match javalite CL) (term (class C0 extends Object ((bool x) (bool y)) ((bool m () (begin (x := true) (y := true)))))))
(test-term-equal (method-lookup (class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true))))) m)
                 (C0 () (begin (x := true) (y := true))))

(test-predicate (redex-match javalite object) (term  (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))))
(test-predicate (redex-match javalite h) (term (mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))])))

(test--> expr-reductions
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool n () true)))
                 (class C2 extends C1 ([bool z]) ((bool m () false))))
                (mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
                mt (raw (addr 0 C0) @ m ()) ret))
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool n () true)))
                 (class C2 extends C1 ([bool z]) ((bool m () false))))
                ((mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C2)])
                (mt [this -> 1])
                false (pop mt ret))))       

(test--> expr-reductions
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool m () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                (mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
                mt (raw (addr 0 C0) @ m ()) ret))
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool m () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                ((mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C1)])
                (mt [this -> 1])
                true (pop mt ret))))

(test--> expr-reductions
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool m () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                (mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
                mt (raw (addr 0 C2) @ m ()) ret))
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool m () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                ((mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C1)])
                (mt [this -> 1])
                true (pop mt ret))))

(test--> expr-reductions
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool o () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                (mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) 
                mt (raw (addr 0 C0) @ m ()) ret))
         (term (((class C0 extends Object ([bool x]) ((bool m () (begin (x := true) (y := true)))))
                 (class C1 extends C0 ([bool y]) ((bool o () true)))
                 (class C2 extends C1 ([bool z]) ((bool n () false))))
                ((mt [0 -> (C0 (Object) (C0 [x 1]) (C1 [y 2]) (C2 [z 3]))]) [1 -> (addr 0 C0)])
                (mt [this -> 1])
                (begin (x := true) (y := true)) (pop mt ret))))

;; cast?
(test-equal (cast? (term (C (Object) (C))) (term Object)) '#t)
(test-equal (cast? (term (C (Object) (C))) (term C1)) '#f)
(test-equal (cast? (term (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term C2)) #t)
(test-equal (cast? (term (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term C1)) #t)
(test-equal (cast? (term (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term Obj)) #t)
(test-equal (cast? (term (C2 (Obj) (C1 [x 1] [y 2]) (C2 [x 3]))) (term x)) #f)

; instanceof*
(test-term-equal (instanceof* (C (Object) (C)) C)
                 true)
(test-term-equal (instanceof* (C (Object) (C) (D)) Object)
                 true)
(test-term-equal (instanceof* (C (Object) (C)) D)
                 false)
(test-term-equal (instanceof* (Object (Object)) D)
                 false)

(test-results)