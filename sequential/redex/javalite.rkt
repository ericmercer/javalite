#lang racket
(require redex/reduction-semantics)

(provide (all-defined-out))

; -----------------------------------------------------
; -------------------- SYNTAX -------------------------
; -----------------------------------------------------

(define-language javalite-surface
  ;; input syntax
  (P (μ (C m)))
  (μ (CL ...))
  (T bool
     unit
     C)
  (CL (class C extends C ([T f] ...) (M ...)))
  (M (T m ([T x] ...) e))
  (e x
     v
     (new C)
     (e $ f)
     (e @ m (e ...))
     (e == e)
     (C e)
     (e instanceof C)
     (x := e)
     (x $ f := e)
     (if e e else e)
     (var T x := e in e)
     (begin e ...)) 
  (x this
     id)
  (f id)
  (m id)
  (C Object
     id)
  (id variable-not-otherwise-mentioned)
  (pointer (addr loc C)
           null)
  (v pointer
     true
     false
     unit
     error)
  (loc number)
  )

(define-extended-language javalite javalite-surface
  (e ....
     (raw v @ m (v ...)))
    ;; eval syntax
  (object ((C [f loc] ...) ...))
  (hv v
      object)
  (h mt
     (h [loc -> hv]))
  (η mt
     (η [x -> loc]))
  (state (μ h η e k))
  (k ret
     (* $ f -> k)
     (* @ m (e ...) -> k)
     (v @ m (v ...) * (e ...) -> k)
     (* == e -> k)
     (v == * -> k)
     (C * -> k)
     (* instanceof C -> k)
     (x := * -> k)
     (x $ f := * -> k)
     (if * e else e -> k)
     (var T x := * in e -> k)
     (begin * (e ...) -> k)
     (pop η k))
  )

; -----------------------------------------------------
; ------------- EXPRESSION REDUCTIONS -----------------
; -----------------------------------------------------

(define expr-reductions
  (reduction-relation
   javalite
   #:domain state
   
   ; variable access
   (--> (μ h η x k)
        (μ h η v k)
        "Variable access"
        (where v (h-lookup h (η-lookup η x))))
   
   ; new
   (--> (μ h η (new C) k)
        (μ h_1 η (addr loc_1 C) k)
        "new"
        (where (([T_0 f_0] ...) ...) (fields-parents+self μ C))
        (where (C_0 ...) (class-parents+self μ C))
        (where ((v_0 ...) ...) ((default-value* (T_0 ...)) ...))
        (where (number_0 ...) ((get-length (T_0 ...)) ...))
        (where ((loc_0 ...) ...) (h-malloc-n* h number_0 ...))
        (where object ((C_0 [f_0 loc_0] ...) ...))
        (where h_0 (h-extend* h [loc_0 -> v_0] ... ...))
        (where loc_1 (h-malloc h_0))
        (where h_1 (h-extend* h_0 [loc_1 -> object])))
   
   ; field access
   (--> (μ h η (e $ f) k)
        (μ h η e (* $ f -> k))
        "field access - object eval")
   (--> (μ h η (addr loc C) (* $ f -> k))
        (μ h η v k)
        "field access"
        (where object (cast (h-lookup h loc) C))
        (where loc_0 (field-lookup object f C))
        (where v (h-lookup h loc_0)))
   
   ; method invocation
   (--> (μ h η (e_0 @ m (e_1 ...)) k)
        (μ h η e_0 (* @ m (e_1 ...) -> k))
        "method invocation - object eval")
   (--> (μ h η v (* @ m (e_0 e_1 ...) -> k))
        (μ h η e_0 (v @ m () * (e_1 ...) -> k))
        "method invocation - arg0 eval")
   (--> (μ h η v_i (v_o @ m (v_a ...) * (e_0 e_1 ...) -> k))
        (μ h η e_0 (v_o @ m (v_a ... v_i) * (e_1 ...) -> k))
        "method invocation - argi eval")
   (--> (μ h η v_o (* @ m () -> k))
        (μ h η (raw v_o @ m ()) k)
        "method invocation - no args")
   (--> (μ h η v_1 (v_o @ m (v_0 ...) * () -> k))
        (μ h η (raw v_o @ m (v_0 ... v_1)) k)
        "method invocation - args")
   (--> (μ h η (raw (addr loc C) @ m (v_x ...)) k)
        (μ h_0 η_0 e_m (pop η k))
        "raw method invocation"
        (where (C_0 C_p ...) (class-list-from-object (h-lookup h loc)))
        (where (any_0 ... (C_t (x_m ...) e_m) error ...)
               ((method-lookup (class-lookup μ C_p) m) ...))
        (where (loc_o loc_x ...) (h-malloc-n h ,(add1 (length (term (v_x ...))))))
        (where h_0 (h-extend* h [loc_o -> (addr loc C_t)] [loc_x -> v_x] ...))
        (where η_0 (η-extend* η [this -> loc_o] [x_m -> loc_x] ...)))
   
   ; equals '==' 
   (--> (μ h η (e_0 == e) k)
        (μ h η e_0 (* == e -> k))
        "equals - l-operand eval")
   (--> (μ h η v (* == e -> k))
        (μ h η e (v == * -> k))
        "equals - r-operand eval")
   (--> (μ h η v_0 (v_1 == * -> k))
        (μ h η v_res k)
        "equals"
        (where v_res ,(->bool (equal? (term v_0) (term v_1)))))
   
   ; typecast
   (--> (μ h η (C e) k)
        (μ h η e (C * -> k))
        "typecast - object eval")
   (--> (μ h η (addr loc C_0) (C_1 * -> k))
        (μ h η (addr loc C_1) k)
        "typecast"
        (where object (h-lookup h loc))
        (side-condition (cast? (term object) (term C_1))))
   
   ; instanceof
   (--> (μ h η (e instanceof C) k)
        (μ h η e (* instanceof C -> k))
        "instanceof - object eval")
   (--> (μ h η (addr loc C_0) (* instanceof C_1 -> k))
        (μ h η v_res k)
        "instanceof"
        (where object (h-lookup h loc))
        (where v_res ,(cast?/->bool (term object) (term C_1))))
  
   ; assign
   (--> (μ h η (x := e) k)
        (μ h η e (x := * -> k))
        "assign -- object eval")
   (--> (μ h η v (x := * -> k))
        (μ h_0 η v k)
        "assign"
        (where loc (η-lookup η x))
        (where h_0 (h-extend* h [loc -> v])))
   
   ; assign Field
   (--> (μ h η (x $ f := e) k)
        (μ h η e (x $ f := * -> k))
        "assign field -- object eval")
   (--> (μ h η v (x $ f := * -> k))
        (μ h_0 η v k)
        "assign field"
        (where loc_0 (η-lookup η x))
        (where (addr loc_1 C) (h-lookup h loc_0))
        (where object (cast (h-lookup h loc_1) C))
        (where loc_2 (field-lookup object f C))
        (where h_0 (h-extend* h [loc_2 -> v])))
 
   ; if-then-else
   (--> (μ h η (if e_p e_t else e_f) k)
        (μ h η e_p (if * e_t else e_f -> k))
        "if-then-else -- object eval")
   (--> (μ h η v (if * e_t else e_f -> k))
        (μ h η ,(if (equal? (term v) (term true)) (term e_t) (term e_f)) k)
        "if-then-else")
   
   ; varriable declaration
   (--> (μ h η (var T x := e_0 in e_1) k)
        (μ h η e_0 (var T x := * in e_1 -> k))
        "variable declaration -- object eval")
   (--> (μ h η v (var T x := * in e_1 -> k))
        (μ h_0 η_0 e_1 (pop η k))
        "variable declaration"
        (where loc_x (h-malloc h))
        (where h_0 (h-extend* h [loc_x -> v]))
        (where η_0 (η-extend* η [x -> loc_x])))
   
   ; begin
   (--> (μ h η (begin) k)
        (μ h η unit k)
        "begin -- empty expression list")
   (--> (μ h η (begin e_0 e_1 ...) k)
        (μ h η e_0 (begin * (e_1 ...) -> k))
        "begin -- e_0 evaluation")
   (--> (μ h η v (begin * (e_i e_i+1 ...) -> k))
        (μ h η e_i (begin * (e_i+1 ...) -> k))
        "begin -- e_i evaluation")
   #;(--> (μ h η v (begin * (e_n) -> k))
        (μ h η e_n (begin * () -> k))
        "begin -- e_n evaluation")
   (--> (μ h η v (begin * () -> k))
        (μ h η v k)
        "begin -- complete")
      
   ; Pop η (close scope)
   (--> (μ h η v (pop η_0 k))
        (μ h η_0 v k)
        "pop η")
   ))

; -----------------------------------------------------
; ------------------ HELPER FUNCTIONS -----------------
; -----------------------------------------------------

(define-metafunction javalite
  get-length : (any ...) -> number
  [(get-length (any_0 ...))
   ,(length (term (any_0 ...)))])
  
(define-metafunction javalite
  default-value : T -> v
  [(default-value bool)
   false]
  [(default-value unit)
   unit]
  [(default-value C)
   null])

(define-metafunction javalite
  default-value* : (T ...) -> (v ...)
  [(default-value* ())
   ()]
  [(default-value* (T_0 T_1 ...))
   ((default-value T_0) (default-value T_1) ...)])
  
(define-metafunction javalite
  h-max : h -> number
  [(h-max mt) -1]
  [(h-max (h [loc -> hv]))
   ,(max (term loc) (term (h-max h)))])

(define-metafunction javalite
  h-malloc : h -> number
  [(h-malloc h)
   ,(add1 (term (h-max h)))])

(define-metafunction javalite
  h-malloc-n-helper : number number -> (loc ...)
  [(h-malloc-n-helper number_b number_c)
   ,(let ([z (term number_b)]) (build-list (term number_c) (lambda (y) (+ y z))))])

(define-metafunction javalite
  h-malloc-n : h number -> (loc ...)
  [(h-malloc-n h number)
   (loc_0 ...)
   (where ((loc_0 ...)) (h-malloc-n* h number))])

(define-metafunction javalite
  internal-h-malloc-n* : number (number ...) -> (number (loc ...) ...)
  [(internal-h-malloc-n* number_b (number_0))
   (number_t (loc_1 ...))
   (where (loc_1 ...) (h-malloc-n-helper number_b number_0))
   (where number_t ,(if (empty? (term (loc_1 ...))) (term number_b) (add1 (apply max (term (loc_1 ...))))))]
  [(internal-h-malloc-n* number_b (number_0 number_1 number_2 ...))
   (number_t (loc_0 ...) (loc_1 ...) ...)
   (where (loc_0 ...) (h-malloc-n-helper number_b number_0))
   (where number_i ,(if (empty? (term (loc_0 ...))) (term number_b) (add1 (apply max (term (loc_0 ...))))))
   (where (number_t (loc_1 ...) ...) (internal-h-malloc-n* number_i (number_1 number_2 ...)))])

(define-metafunction javalite
  h-malloc-n* : h number ... -> ((loc ...) ...)
  [(h-malloc-n* h number_0 ...)
   ((loc_0 ...) ...)
   (where (number (loc_0 ...) ...) (internal-h-malloc-n* (h-malloc h) (number_0 ...)))])

(define-metafunction javalite
  storelike-lookup : any any -> any
  [(storelike-lookup mt any_0)
   ,(error 'storelike-loopup "~e not found in ~e" (term any_0) (term mt))]
  [(storelike-lookup (any_0 [any_t -> any_ans]) any_t)
   any_ans]
  [(storelike-lookup (any_0 [any_k -> any_v]) any_t)
   (storelike-lookup any_0 any_t)
   (side-condition (not (equal? (term any_k) (term any_t))))])

(define (id-<= a b)
  (string<=? (symbol->string a) (symbol->string b)))
(define (storelike-extend <= storelike k hv)
  (match storelike
    ['mt `(mt [,k -> ,hv])]
    [`(,storelike [,ki -> ,hvi])
     (cond
       [(equal? k ki)
        `(,storelike [,ki -> ,hv])]
       [(<= k ki)
        `(,(storelike-extend <= storelike k hv) [,ki -> ,hvi])]
       [else
        `((,storelike [,ki -> ,hvi]) [,k -> ,hv])])]))     
  
(define (storelike-extend* <= storelike extend*)
  (match extend*
    ['() storelike]
    [`([,k -> ,hv] . ,extend*)
     (storelike-extend* <= (storelike-extend <= storelike k hv) extend*)]))

(define-metafunction javalite
  h-lookup : h loc -> hv
  [(h-lookup h loc)
   (storelike-lookup h loc)])

(define-metafunction javalite
  h-extend* : h [loc -> hv] ... -> h
  [(h-extend* h [loc -> hv] ...)
   ,(storelike-extend* <= (term h) (term ([loc -> hv] ...)))])

(define-metafunction javalite
  η-lookup : η x -> loc
  [(η-lookup η x)
   (storelike-lookup η x)])

(define-metafunction javalite
  η-extend* : η [x -> loc] ... -> η
  [(η-extend* η [x -> loc] ...)
   ,(storelike-extend* id-<= (term η) (term ([x -> loc] ...)))])

(define-metafunction javalite
  restricted-field-lookup : object f -> loc
  [(restricted-field-lookup (
                  (C_0 [f_0 loc_0] ...) ...
                  (C_t [f_t0 loc_t0] ...
                       [f_target loc_target]
                       [f_t1 loc_t1] ...)
                  (C_1 [f_1 loc_1] ...) ...)
                 f_target)
   loc_target
   ;; Allows for redefinition and restricts matching
   ;; to be the most recent definition by current cast.
   (side-condition
    (not (member (term f_target)
                 (term (f_t1 ... f_1 ... ...)))))])

(define-metafunction javalite
  field-lookup : object f C -> loc
  [(field-lookup object f_target C)
   (restricted-field-lookup (restrict-object object C) f_target)])

(define-metafunction javalite
  restrict-object : object C -> object
  [(restrict-object (    (C_0 [f_0 loc_0] ...) ...
                         (C_c [f_c loc_c] ...)
                         (C_1 [f_1 loc_1] ...) ...) C)
   (    (C_0 [f_0 loc_0] ...) ...
        (C_c [f_c loc_c] ...))
   (side-condition (equal? (term C) (term C_c)))])

(define-metafunction javalite
  class-name : CL -> C
  [(class-name (class C_t extends C ([T f] ...) (M ...)))
   C_t])

(define-metafunction javalite
  parent-name : CL -> C
  [(parent-name (class C extends C_p ([T f] ...) (M ...)))
   C_p])

(define-metafunction javalite
  field-list : CL -> ([T f] ...)
  [(field-list (class C extends C_p ([T f] ...) (M ...)))
   ([T f] ...)])

(define-metafunction javalite
  class-list-extend : (C ...) C -> (C ...)
  [(class-list-extend (C_0 ...) C_1)
   (C_0 ... C_1)])

(define-metafunction javalite
  class-lookup : μ C -> CL
  [(class-lookup (CL_0 ... CL_1 CL_2 ...) C)
   CL_1 
   (side-condition (equal? (term (class-name CL_1)) (term C)))])

(define-metafunction javalite
  class-list-from-object : object -> (C ...)
  [(class-list-from-object ((C_1 [f_1 loc_1] ...) ...)) 
   (C_1 ...)])

(define-metafunction javalite
  class-parents+self : μ C -> (C ...)
  [(class-parents+self μ Object)
   (class-list-extend () Object)]
  ; id retricts out the base case above
  [(class-parents+self μ id)
   (class-list-extend (class-parents+self μ C_p) id)
   (where CL (class-lookup μ id))
   (where C_p (parent-name CL))])

(define-metafunction javalite
  field-lists-extend : (([T f] ...) ...) ([T f] ...) -> (([T f] ...) ...)
  [(field-lists-extend  (([T_0 f_0] ...) ...) ([T_1 f_1] ...))
   (([T_0 f_0] ...) ... ([T_1 f_1] ...))])
  
(define-metafunction javalite
  fields-parents+self : μ C -> (([T f] ...) ...)
  [(fields-parents+self μ Object)
   (field-lists-extend () ())]
  ; id restricts out the base case above
  [(fields-parents+self μ id)
   (field-lists-extend (fields-parents+self μ C_p) ([T f] ...))
   (where CL (class-lookup μ id))
   (where C_p (parent-name CL))
   (where ([T f] ...) (field-list CL))])

(define-metafunction javalite
  method-name : M -> m
  [(method-name (T_0 m ([T_1 x] ...) e))
   m])

(define-metafunction javalite
  method-expression : M -> e
  [(method-expression (T_0 m ([T_1 x] ...) e))
   e])

(define-metafunction javalite
  method-args : M -> (x ...)
  [(method-args (T_0 m ([T_1 x] ...) e))
   (x ...)])

(define-metafunction javalite
  method-lookup : CL m -> any
  [(method-lookup (class C_0 extends C_1 ([T x] ...) (M_0 ... M_t M_1 ...)) m)
   (C_0 (method-args M_t) (method-expression M_t))
   (side-condition (equal? (term (method-name M_t)) (term m)))]
  [(method-lookup (class C_0 extends C_1 ([T x] ...) (M ...)) m)
   error
   (side-condition (equal? (findf (λ (i) (equal? (term (method-name ,i)) (term m)))
                                   (term (M ...))) #f))])

(define (->bool v)
    (if v
        'true
        'false))

(define-metafunction javalite
  cast : object C -> object
  [(cast (    (C_2 [f_2 loc_2] ...) ... 
              (C_3 [f_3 loc_3] ...) 
              (C_4 [f_4 loc_4] ...) ...) C_3)
   (    (C_2 [f_2 loc_2] ...) ... 
        (C_3 [f_3 loc_3] ...) 
        (C_4 [f_4 loc_4] ...) ...)])

(define (cast? object C_t)
  (define inner-cast?
    (term-match/single
     javalite
     [((C_2 [f_2 loc_2] ...) ...)
      (term (C_2 ...))]))
  (if (member C_t (inner-cast? object)) #t #f))

(define (cast?/->bool object C_t)
  (->bool (cast? object C_t)))

(define-metafunction javalite
     instanceof* : object C -> v
     [(instanceof* ((C_2 [f_2 loc_2] ...) ...) C_t)
      ,(->bool (member (term C_t) (term (C_2 ...))))])

(define-metafunction javalite
  inject : P -> state
  [(inject (μ (C m)))
   (μ mt mt ((new C) @ m ()) ret)])

(define-metafunction javalite
  inject/with-state : state m -> state
  [(inject/with-state (μ h η e k) m)
   (μ h η (e @ m ()) ret)])
   
