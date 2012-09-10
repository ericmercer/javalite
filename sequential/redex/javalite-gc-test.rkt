#lang racket
(require redex/reduction-semantics
         unstable/markparam
         "javalite.rkt"
         "javalite-gc.rkt")

; heap-scan
(test-equal
 (mark-parameterize 
  ([inspecting 0])
  (heap-scan (term mt) 0))
 empty)

(test-equal
 (term (h-lookup (mt [0 -> null]) 0))
 (term null))

(test-equal
 (scan (term (mt [0 -> null])) (term null))
 empty)

(test-equal
 (heap-scan (term (mt [0 -> null])) 0)
 (list 0))

(test-equal
 (heap-scan (term (mt [0 -> (Obj (Obj [x 1]))])) 0)
 (list 0 1))

(test-equal
 (heap-scan (term (mt [0 -> (Obj (Obj [x 0]))])) 0)
 (list 0))

; scan
(define-syntax-rule (test-scan (loc ...) t)
  (test-equal (scan 'mt (term t)) (list loc ...)))

(test-scan (0) 0)
(test-scan (0 1) (Obj (C1 [x 0]) (C2 [y 1])))
(test-scan () true)
(test-scan () false)
(test-scan () unit)
(test-scan () null)
(test-scan () error)
(test-scan () x)
(test-scan () some-id)
(test-scan () (new C1))
(test-scan (3) ((addr 3 C) $ x))
(test-scan (0 1) ((addr 0 C) @ f ((addr 1 D))))
(test-scan (0 1) (raw (addr 0 C) @ f ((addr 1 D))))
(test-scan (0 1) ((addr 0 C) == (addr 1 D)))
(test-scan (0) (C2 (Obj) (C1 [x 0])))
(test-scan (0) ((addr 0 Obj) instanceof C1))
(test-scan (0) (x := (addr 0 C)))
(test-scan (0) (x $ f := (addr 0 C)))
(test-scan (0 1 2) (if (addr 0 C) (addr 1 D) else (addr 2 E)))
(test-scan (0 1) (var C1 x := (addr 0 C) in (addr 1 D)))
(test-scan (0 1) (begin (addr 0 C) (addr 1 D)))
(test-scan (0) (C1 m ([C2 x]) (addr 0 Obj)))
(test-scan (0 1) 
           (class C1 extends Obj ([Obj g])
             ((C1 m1 ([C2 x]) (addr 0 Obj))
              (C1 m2 ([C2 x]) (addr 1 Obj)))))
(test-scan (0 1 2 3) 
           ((class C1 extends Obj ([Obj g])
              ((C1 m1 ([C2 x]) (addr 0 Obj))
               (C1 m2 ([C2 x]) (addr 1 Obj))))
            (class C1 extends Obj ([Obj g])
              ((C1 m1 ([C2 x]) (addr 2 Obj))
               (C1 m2 ([C2 x]) (addr 3 Obj))))))
(test-scan () mt)
(test-scan (0) (mt [x -> 0]))
(test-scan (0 1) ((mt [x -> 0]) [y -> 1]))

(define k0 (term (* == (addr 0 Obj) -> ret)))
(test-scan () ret)
(test-scan (0) ,k0)
(test-scan (0) (* $ f -> ,k0))
(test-scan (1 0) (* @ m ((addr 1 C)) -> ,k0))
(test-scan (1 2 3 0) ((addr 1 Obj) @ m ((addr 2 Obj)) * ((addr 3 Obj)) -> ,k0))
(test-scan (1 0) (* == (addr 1 Obj) -> ,k0))
(test-scan (1 0) ((addr 1 Obj) == * -> ,k0))
(test-scan (0) (C1 * -> ,k0))
(test-scan (0) (* instanceof C1 -> ,k0))
(test-scan (0) (x := * -> ,k0))
(test-scan (0) (x $ f := * -> ,k0))
(test-scan (1 2 0) (if * (addr 1 Obj) else (addr 2 Obj) -> ,k0))
(test-scan (1 0) (var K1 x := * in (addr 1 Obj) -> ,k0))
(test-scan (1 0) (pop (mt [x -> 1]) ,k0))
(test-scan (1 0) (begin * ((addr 1 Obj)) -> ,k0))
(test-scan () ((class C1 extends Object ([C1 n]) ())))
(test-scan () ((class C1 extends Object () ((C1 m()(begin true))))))

; 4 is missing because we do not scan the heap and test-scan uses an empty heap
(test-scan (0 1 2 3 5 6 7)
           ( ((class C1 extends Obj ([Obj g])
                ((C1 m1 ([C2 x]) (addr 0 Obj))
                 (C1 m2 ([C2 x]) (addr 1 Obj))))
              (class C1 extends Obj ([Obj g])
                ((C1 m1 ([C2 x]) (addr 2 Obj))
                 (C1 m2 ([C2 x]) (addr 3 Obj)))))
             (mt [0 -> (Obj (C1 [x 4]))])
             (mt [x -> 5])
             (addr 6 Obj)
             (* == (addr 7 Obj) -> ret) ))

; mark

(test-equal (mark (term ( ((class C1 extends Obj ([Obj g])
                             ((C1 m1 ([C2 x]) (addr 0 Obj))
                              (C1 m2 ([C2 x]) (addr 1 Obj))))
                           (class C1 extends Obj ([Obj g])
                             ((C1 m1 ([C2 x]) (addr 2 Obj))
                              (C1 m2 ([C2 x]) (addr 3 Obj)))))
                          (mt [0 -> (Obj (C1 [x 4]))])
                          (mt [x -> 5])
                          (addr 6 Obj)
                          (* == (addr 7 Obj) -> ret) )))
            (list 0 4 1 2 3 5 6 7))

; subst

(define-syntax-rule (test-subst t0 ([from -> to] ...) t1)
  (test-equal (subst (make-hasheq (list (cons from to) ...)) (term t0)) (term t1)))

(test-subst 0
            ([0 -> 1])
            1)
(test-subst (Obj (C1 [x 0]) (C2 [y 1])) 
            ([0 -> 1] [1 -> 0])
            (Obj (C1 [x 1]) (C2 [y 0])))

; heap->hash

(test-equal (heap->hash (term mt)) #hasheq())
(test-equal (heap->hash (term (mt [0 -> error]))) #hasheq([0 . error]))
(test-equal (heap->hash (term ((mt [0 -> error]) (0 -> unit)))) #hasheq([0 . unit]))
(test-equal (heap->hash (term ((mt [0 -> error]) (1 -> unit)))) #hasheq([0 . error] [1 . unit]))

; list->heap

(test-equal (list->heap '([0 . error] [1 . unit]))
            '((mt [0 -> error]) (1 -> unit)))

; hash-reverse

(test-equal (hash-reverse (hasheq 0 'a 1 'b)) (hasheq 'a 0 'b 1))

; compact-heap

(define-syntax-rule (test-compact-heap (ordered-loc ...) initial-heap ([old-loc -> new-loc] ...) expected-new-heap)
  (let-values ([(renaming new-heap) (compact-heap (list ordered-loc ...) (term initial-heap))])
    (test-equal renaming (make-immutable-hasheq (list (cons old-loc new-loc) ...)))
    (test-equal new-heap (term expected-new-heap))))

(test-compact-heap () 
                   mt
                   ()
                   mt)
(test-compact-heap (0)
                   (mt [0 -> error])
                   ([0 -> 0])
                   (mt [0 -> error]))
(test-compact-heap (1 0)
                   ((mt [0 -> unit]) (1 -> error))
                   ([0 -> 1] [1 -> 0])
                   ((mt [0 -> error]) (1 -> unit)))
(test-compact-heap (1 0)
                   ((mt [0 -> (Obj (C [x 1]))]) [1 -> true])
                   ([0 -> 1] [1 -> 0]) 
                   ((mt [0 -> true]) [1 -> (Obj (C [x 0]))]))

; compact does not effect literals
(test-compact-heap (0 1)
                   ((mt [0 -> error]) (1 -> error))
                   ([0 -> 0] [1 -> 1])
                   ((mt [0 -> error]) (1 -> error)))

; basic compacting: if the objects are the same, they are collapsed
(test-compact-heap (0 1)
                   ((mt [0 -> (Obj (C [x 0]))]) (1 -> (Obj (C [x 0]))))
                   ([0 -> 0] [1 -> 0])
                   (mt [0 -> (Obj (C [x 0]))]))

; If they are cast differently, they are not collapsed
(test-compact-heap (0 1)
                   ((mt [0 -> (Obj0 (C [x 0]))]) (1 -> (Obj1 (C [x 0]))))
                   ([0 -> 0] [1 -> 1])
                   ((mt [0 -> (Obj0 (C [x 0]))]) (1 -> (Obj1 (C [x 0])))))

; compacting prefers the first one
(test-compact-heap (0 1)
                   ((mt [0 -> (Obj (C [x 1]))]) (1 -> (Obj (C [x 1]))))
                   ([0 -> 0] [1 -> 0])
                   (mt [0 -> (Obj (C [x 0]))]))

; compact-once

(test-equal 
 (compact-once 
  (term ( ((class C1 extends Obj ([Obj g])
             ((C1 m1 ([C2 x]) (addr 0 Obj)))))
          ((mt [0 -> (addr 0 Obj)]) (1 -> (addr 0 Obj)))
          (mt [x -> 1])
          (addr 1 Obj)
          (* == (addr 0 Obj) -> ret) )))
 (term ( ((class C1 extends Obj ([Obj g])
            ((C1 m1 ([C2 x]) (addr 0 Obj)))))
         (mt [0 -> (addr 0 Obj)])
         (mt [x -> 0])
         (addr 0 Obj)
         (* == (addr 0 Obj) -> ret) )))

; heap-size
(test-equal (heap-size (term (() mt mt null ret))) 0)
(test-equal (heap-size (term (() (mt [0 -> error]) mt null ret))) 1)
(test-equal (heap-size (term (() ((mt [0 -> error]) [1 -> unit]) mt null ret))) 2)

; reorder-heap
(define-syntax-rule (test-reorder-heap (loc ...) h ([old -> new] ...) expected-nh)
  (local [(define-values (renaming actual-nh) (reorder-heap (list loc ...) (term h)))]
    (test-equal renaming (make-immutable-hasheq (list (cons old new) ...)))
    (test-equal actual-nh (term expected-nh))))

(test-reorder-heap () mt 
                   () mt)
(test-reorder-heap (1 0) ((mt [0 -> null]) (1 -> error))
                   ([1 -> 0] [0 -> 1])
                   ((mt [0 -> error]) (1 -> null)))
(test-reorder-heap (1 0 1) ((mt [0 -> null]) (1 -> error))
                   ([1 -> 0] [0 -> 1])
                   ((mt [0 -> error]) (1 -> null)))
(test-reorder-heap (1 0) (((mt [0 -> null]) (1 -> error)) (2 -> (Obj (C [x 0]))))
                   ([1 -> 0] [0 -> 1])
                   ((mt [0 -> error]) (1 -> null)))
(test-reorder-heap (1 0 2) (((mt [0 -> null]) (1 -> error)) (2 -> (Obj (C [x 0]))))
                   ([1 -> 0] [0 -> 1] [2 -> 2])
                   (((mt [0 -> error]) (1 -> null)) (2 -> (Obj (C [x 1])))))

; reorder
(define-syntax-rule (test-reorder s ns)
  (test-equal (reorder (term s)) (term ns)))

(test-reorder 
 ( ((class C1 extends Obj ([Obj g])
      ((C1 m1 ([C2 x]) (addr 0 Obj)))))
   (((mt [0 -> (Obj (C [x 0]))]) [1 -> (Obj (C [x 0]))]) [2 -> (addr 0 Obj)])
   (mt [x -> 2])
   (addr 0 Obj)
   (* == (addr 0 Obj) -> ret))
 
 ( ((class C1 extends Obj ([Obj g])
      ((C1 m1 ([C2 x]) (addr 0 Obj)))))
   ((mt [0 -> (Obj (C [x 0]))]) [1 -> (addr 0 Obj)])
   (mt [x -> 1])
   (addr 0 Obj)
   (* == (addr 0 Obj) -> ret) ))

; Location 0 is not referenced
(test-reorder 
 ( ((class C1 extends Obj ([Obj g])
      ((C1 m1 ([C2 x]) (addr 1 Obj)))))
   (((mt [0 -> (Obj (C [x 1]))]) [1 -> (Obj (C [x 1]))]) [2 -> (addr 1 Obj)])
   (mt [x -> 2])
   (addr 1 Obj)
   (* == (addr 1 Obj) -> ret))
 
 ( ((class C1 extends Obj ([Obj g])
      ((C1 m1 ([C2 x]) (addr 0 Obj)))))
   ((mt [0 -> (Obj (C [x 0]))]) [1 -> (addr 0 Obj)])
   (mt [x -> 1])
   (addr 0 Obj)
   (* == (addr 0 Obj) -> ret) ))

; compact

(test-equal 
 (compact
  (term ( ((class C1 extends Obj ([Obj g])
             ((C1 m1 ([C2 x]) (addr 1 Obj)))))
          ((mt [0 -> (Obj (C [x 1]))]) (1 -> (Obj (C [x 1]))))
          (mt [x -> 1])
          (addr 1 Obj)
          (* == (addr 1 C) -> ret) )))
 (term ( ((class C1 extends Obj ([Obj g])
            ((C1 m1 ([C2 x]) (addr 0 Obj)))))
         (mt [0 -> (Obj (C [x 0]))])
         (mt [x -> 0])
         (addr 0 Obj)
         (* == (addr 0 C) -> ret) )))

; gc

(test-equal 
 (gc 
  (term ( ((class C1 extends Obj ([Obj g])
             ((C1 m1 ([C2 x]) (addr 1 Obj)))))
          (((mt [0 -> (Obj (C [x 1]))]) (1 -> (Obj (C [x 1])))) [2 -> error])
          (mt [x -> 1])
          (addr 1 Obj)
          (* == (addr 1 Obj) -> ret) )))
 (term ( ((class C1 extends Obj ([Obj g])
            ((C1 m1 ([C2 x]) (addr 0 Obj)))))
         (mt [0 -> (Obj (C [x 0]))])
         (mt [x -> 0])
         (addr 0 Obj)
         (* == (addr 0 Obj) -> ret) )))

(local [(define μ_1
          (term ((class C1 extends Object ([C1 n]) ()))))
        (define h_1
          (term (((((((mt [0 -> (C1 (Object) (C1 [n 5]))])
                      [1 -> (C1 (Object) (C1 [n 6]))])
                     [2 -> (C1 (Object) (C1 [n 3]))])
                    [3 -> null])
                   [4 -> (addr 0 C1)])
                  [5 -> (addr 1 C1)])
                 [6 -> (addr 2 C1)])))
        (define h_2
          (term (((((((mt [0 -> (C1 (Object) (C1 [n 5]))])
                      [1 -> (C1 (Object) (C1 [n 6]))])
                     [2 -> null])
                    [3 -> (C1 (Object) (C1 [n 2]))])
                   [4 -> (addr 0 C1)])
                  [5 -> (addr 1 C1)])
                 [6 -> (addr 3 C1)])))]
  
  (test-predicate (redex-match javalite μ) μ_1)
  (test-predicate (redex-match javalite h) h_1)
  (test-predicate (redex-match javalite h) h_2)
  
  (test-equal
   (gc
    (term (,μ_1
           ,h_1 
           (mt [x -> 4]) 
           x 
           ret)))
   (gc
    (term (,μ_1 
           ,h_1 
           (mt [x -> 4]) 
           x 
           ret))))
  
  ; Compact needs to compute a fix-point
  (test-equal
   (compact
    (term (,μ_1 
           ,h_1 
           (mt [x -> 4]) 
           x 
           ret)))
   (compact
    (term (,μ_1 
           ,h_2 
           (mt [x -> 4]) 
           x 
           ret))))
  
  (test-equal
   (gc
    (term (,μ_1 
           ,h_1 
           (mt [x -> 4]) 
           x 
           ret)))
   (gc
    (term (,μ_1 
           ,h_2 
           (mt [x -> 4]) 
           x 
           ret)))) )

; Compact does not go into an infinite loop
(local [(define μ_1
          (term ((class C1 extends Object ([C1 n]) ()))))
        (define h_1
          (term ((mt [0 -> (C1 (Object) (C1 [n 1]))])
                 [1 -> (C1 (Object) (C1 [n 0]))])))
        (define t_1
          (term (,μ_1 
                 ,h_1 
                 (mt [x -> 0]) 
                 x 
                 ret)))
        (define t_2
          (term (,μ_1 
                 ,h_1 
                 (mt [x -> 1]) 
                 x 
                 ret)))]
  
  (test-equal (compact-once t_1) t_1)
  (test-equal (compact-once t_2) t_1)
  (test-equal (compact t_1) t_1)
  (test-equal (compact t_2) t_1)
  (test-equal (gc t_1) t_1))

(define t_1
  (term ( ((class C1 extends Object ([C1 n]) ()))
          ((((((((((((((mt (0 -> (ChurchTest (Object) (ChurchTest))))
                       (1 -> (addr 0 ChurchTest)))
                      (2 -> (addr 12 Variable)))
                     (3 -> null))
                    (4 -> null))
                   (5 -> null))
                  (6 -> null))
                 (7 -> null))
                (8 -> null))
               (9 -> null))
              (10
               ->
               (Church
                (Object)
                (Church (x 2) (f 3) (m 4) (n 5) (g 6) (h 7) (u 8) (zero 9)))))
             (11 -> (addr 10 Church)))
            (12 -> (Variable (Object) (LambdaTerm) (Variable))))
           (13 -> (Variable (Object) (LambdaTerm) (Variable))))
          (mt (this -> 11))
          (addr 13 Variable)
          (this $ f := * -> (begin * ((this $ m := (new Variable)) (this $ n := (new Variable)) (this $ g := (new Variable)) (this $ h := (new Variable)) (this $ u := (new Variable)) (this $ zero := ((new Abstraction) @ construct-x-t ((this $ f) ((new Abstraction) @ construct-x-t ((this $ x) (this $ x))))))) -> (pop (mt (this -> 1)) (var Church c := * in c -> (pop mt ret))))))))

(define t_2
  (term ( ((class C1 extends Object ([C1 n]) ()))
          (((((((((((((mt (0 -> (addr 1 Church)))
                      (1
                       ->
                       (Church
                        (Object)
                        (Church (x 2) (f 4) (m 5) (n 6) (g 7) (h 8) (u 9) (zero 10)))))
                     (2 -> (addr 3 Variable)))
                    (3 -> (Variable (Object) (LambdaTerm) (Variable))))
                   (4 -> null))
                  (5 -> null))
                 (6 -> null))
                (7 -> null))
               (8 -> null))
              (9 -> null))
             (10 -> null))
            (11 -> (addr 12 ChurchTest)))
           (12 -> (ChurchTest (Object) (ChurchTest))))
          (mt (this -> 0))
          (addr 3 Variable)
          (this $ f := * -> (begin * ((this $ m := (new Variable)) (this $ n := (new Variable)) (this $ g := (new Variable)) (this $ h := (new Variable)) (this $ u := (new Variable)) (this $ zero := ((new Abstraction) @ construct-x-t ((this $ f) ((new Abstraction) @ construct-x-t ((this $ x) (this $ x))))))) -> (pop (mt (this -> 11)) (var Church c := * in c -> (pop mt ret))))))))
(test-predicate (redex-match javalite state) t_1)

(test-equal (gc t_1) t_2)

; Typed pointers coalesce when they are equivalent
(local [(define μ_1
          (term ((class C1 extends Object ([C1 n]) ()))))
        (define h_1
          (term ((((mt [0 -> (addr 2 C1)])
                   [1 -> (addr 2 C1)])
                  [2 -> (C1 (Object) (C1 [C1 3]))])
                 [3 -> null])))
        (define t_1
          (term (,μ_1 
                 ,h_1 
                 ((mt [x -> 0]) [y -> 1]) 
                 x 
                 ret)))
        (define t_2
          (term (,μ_1 
                 (((mt [0 -> (addr 1 C1)])
                   [1 -> (C1 (Object) (C1 [C1 2]))])
                  [2 -> null])
                 ((mt [x -> 0]) [y -> 0]) 
                 x 
                 ret)))]

  (test-equal (gc t_1) t_2))

(test-results)

