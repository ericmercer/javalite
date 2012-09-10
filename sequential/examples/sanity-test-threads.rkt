#lang racket
(require redex/reduction-semantics
         "../util.rkt"
         "../javalite-threaded.rkt"
         "../javalite-threaded-gc.rkt")


(define sanity-test
  (term (((class C0 extends Object 
           ([bool x] [bool y])
           ((bool m () 
                  (begin (this $ x := true) (this $ y := true) this)))))
         (C0 m) )))

(test-predicate (redex-match lang P) sanity-test)
   
(define initial-term (term (inject ,sanity-test)))
(test-predicate (redex-match lang gstate) initial-term)
(test-equal (gc initial-term) initial-term)

(define intermediate-states 0)
(define duplicate-states 0)
(define answer-g
  (apply-reduction-relation/generator
   global-reductions
   initial-term
   (compose (λ (visited?)
              (if visited?
                  (set! duplicate-states
                        (add1 duplicate-states))
                  (set! intermediate-states
                        (add1 intermediate-states)))
              visited?)
            (make-hash-visited?))
   gc))

(define (display-xy i xy)
  (match-define (list x y) xy)
  (printf "~a. this $ x = ~a, this $ y = ~a\n" i x y))

(define LIMIT +inf.0)

(define (field-lookup* h η f)
    (term (h-lookup h (field-lookup (h-lookup h (η-lookup η this)) f))))

(define state->xy  
  (term-match/single
   lang
   [(μ h (η object ret))
    (term ((h-lookup h (field-lookup object x))
           (h-lookup h (field-lookup object y))))]
   [any
    #f]))

(printf "Running answers:\n")
(define answers
  (for/fold ([ans (set)])
    ([a (in-producer answer-g #f)]
     [i (in-range LIMIT)])
    (set-add ans a)))

(printf "\nIntermediate States: ~a\n" intermediate-states)
(printf "Duplicate States: ~a\n" duplicate-states)

(printf "\nUnique answers:\n")
(for ([xy (in-set answers)]
      [i (in-naturals)])
  (printf "State ~a:\n~a\n" i xy))