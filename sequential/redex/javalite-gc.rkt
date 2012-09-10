#lang racket
(require redex/reduction-semantics
         unstable/markparam
         "javalite.rkt")
(provide (all-defined-out))

(define inspecting (mark-parameter))

(define (h-lookup* h l)
  #;(term (h-lookup ,h ,l))
  (with-handlers ([exn? (λ (x)
                          #;(printf "Failed h-lookup on ~a in ~a\n" h l) 
                          (term false))])
    (term (h-lookup ,h ,l))))

(define (heap-scan h loc)
  (if (member loc (mark-parameter-all inspecting))
      empty
      (mark-parameterize 
       ([inspecting loc])
       (list*
        loc
        (scan h (h-lookup* h loc))))))

(define (scan h t)
  (define-syntax-rule (scan* . r)
    (append-map inner-scan (term r)))
  
  (define inner-scan
    (term-match/single
     javalite
     ; loc
     [loc
      (heap-scan h (term loc))]
     ; (object 
     [(C_0 (C_1 [f loc] ...) ...)
      (scan* loc ... ...)]
     ; (pointer
     [(addr loc C)
      (scan* loc)]
     [v
      empty]
     ; (e 
     [x 
      empty]
     [(new C)
      empty]
     [(e $ f)
      (scan* e)]
     [(e_0 @ m (e_1 ...))
      (scan* e_0 e_1 ...)]
     [(raw v_0 @ m (v_1 ...))
      (scan* v_0 v_1 ...)]
     [(e_0 == e_1)
      (scan* e_0 e_1)]
     [(C e)
      (scan* e)]
     [(e instanceof C)
      (scan* e)]
     [(x := e)
      (scan* e)]
     [(x $ f := e)
      (scan* e)]
     [(if e_0 e_1 else e_2)
      (scan* e_0 e_1 e_2)]
     [(var T x := e_0 in e_1)
      (scan* e_0 e_1)]
     [(begin e ...)
      (scan* e ...)]
     ; (M 
     [(T_0 m ([T_1 x] ...) e)
      (scan* e)]
     ; (CL 
     [(class C_0 extends C_1 ([T f] ...) (M ...))
      (scan* M ...)]
     ; (μ 
     [(CL ...)
      (scan* CL ...)]
     ; (η 
     [mt
      empty]
     [(η [x -> loc])
      (scan* η loc)]
     ; (k 
     [ret
      empty]
     [(* $ f -> k)
      (scan* k)]
     [(* @ m (e ...) -> k)
      (scan* e ... k)]
     [(v_0 @ m (v_1 ...) * (e ...) -> k)
      (scan* v_0 v_1 ... e ... k)]
     [(* == e -> k)
      (scan* e k)]
     [(v == * -> k)
      (scan* v k)]
     [(C * -> k)
      (scan* k)]
     [(* instanceof C -> k)
      (scan* k)]
     [(x := * -> k)
      (scan* k)]
     [(x $ f := * -> k)
      (scan* k)]
     [(if * e_0 else e_1 -> k)
      (scan* e_0 e_1 k)]
     [(var T x := * in e -> k)
      (scan* e k)]
     [(pop η k)
      (scan* η k)]
     [(begin * (e ...) -> k)
      (scan* e ... k)]
     ; (state
     [(μ h η e k)
      (scan* μ η e k)]))
  
  (inner-scan t))

(define mark
  (term-match/single
   javalite
   [(μ h η e k)
    (scan (term h)
          (term (μ h η e k)))]))

; Warning: Deeply relies on numbers only being locations
(define (subst renaming t)
  (let loop ([t t])
    (match t
      [(? number? n) (hash-ref renaming n)]
      [(list) t]
      [(list-rest t0 t1)
       (cons (loop t0) (loop t1))]
      [else t])))

(define (heap->hash h)
  (let loop ([h h])
    (match h
      ['mt (hasheq)]
      [`(,h [,loc -> ,hv])
       (hash-set (loop h) loc hv)])))

(define (list->heap l)
  (for/fold ([h 'mt])
    ([(loc hv) (in-dict l)])
    `(,h [,loc -> ,hv])))

(define (hash-reverse h)
  (for/hasheq ([(k hv) (in-hash h)])
    (values hv k)))

(define (hash->sorted-list h)
  (for/list ([k (sort (hash-keys h) <=)])
    (cons k (hash-ref h k))))

(define (compact-heap order h)
  (define-values (old->new sorted-h)
    (reorder-heap order h))
  (define sorted-hl (hash->sorted-list (heap->hash sorted-h)))
  (define new->old (hash-reverse old->new))
  
  (define seen (make-hash))
  (define new-old->new (make-hasheq))
  (define modifications (make-hasheq))
  (define skip 0)
  (define new-hl
    (filter-map
     (match-lambda
       [(and p (cons new hv))
        (define old (hash-ref new->old new))
        (define new-new (- new skip))
        (hash-set! modifications new new-new)
        (hash-set! new-old->new old new-new)
        (if (list? hv) ; is an object? or object pointer
            (if (hash-has-key? seen hv)
                (local [(define replacement (hash-ref seen hv))]
                  (set! skip (add1 skip))
                  (hash-set! new-old->new old replacement)
                  (hash-set! modifications new replacement)
                  #f)
                (let ()
                  (hash-set! seen hv new-new)
                  (cons new-new hv)))
            (cons new-new hv))])
     sorted-hl))
  #;(printf "\tmod = ~v\n" modifications)
  (define replaced-h1
    (map 
     (match-lambda
       [(cons new hv)
        (define nhv (subst modifications hv))
        #;(printf "\t~a -> ~a -> ~a\n" new hv nhv)
        (cons new nhv)])
     new-hl))
  
  (values (make-immutable-hasheq (hash->list new-old->new))  (list->heap replaced-h1)))

(define compact-once
  (match-lambda
    [(and s (list mu h eta e k))
     (local [(define order (mark s))
             (define-values (renaming nh) (compact-heap order h))]
       (list (subst renaming mu)
             nh
             (subst renaming eta)
             (subst renaming e)
             (subst renaming k)))]))

(define heap-size
  (match-lambda
    [`(,_ ,h ,_ ,_ ,_)
     (let loop ([h h] [s 0])
       (match h
         [`mt s]
         [`(,h [,loc -> ,hv]) (loop h (add1 s))]))]))

(define (reorder-heap order h)
  (let loop ([seen (seteq)]
             [make-nh (λ (renaming) `mt)]
             [renaming (hasheq)]
             [next-loc 0]
             [order order])
    (match order
      [(list) (values renaming (make-nh renaming))]
      [(list-rest loc order)
       (if (set-member? seen loc)
           (loop seen make-nh renaming next-loc order)
           (loop (set-add seen loc)
                 (λ (renaming)
                   (term (,(make-nh renaming) 
                          [,next-loc -> ,(subst renaming (h-lookup* h loc))])))
                 (hash-set renaming loc next-loc)
                 (add1 next-loc)
                 order))])))

(define reorder
  (match-lambda
    [(and s `(,mu ,h ,eta ,e ,k))
     (define order (mark s))
     (define-values (renaming nh) (reorder-heap order h))
     (list (subst renaming mu)
           nh
           (subst renaming eta)
           (subst renaming e)
           (subst renaming k))]))

(define (compact t) 
  (let loop ([tz (heap-size t)]
             [t t])
    #;(printf "Compacting\n")
    (define nt (compact-once t))
    (define ntz (heap-size nt))
    (if (ntz . < . tz)
        (loop ntz nt)
        (reorder nt))))

; XXX Currently does not remove things that will not be referenced from the environment
;     but that could be part of the semantics a la safe for space
(define (gc s)
  (compact (reorder s)))
