#lang racket
(require redex/reduction-semantics
         racket/generator
         "javalite.rkt")
(provide (all-defined-out))

(define print-state
  (term-match/single
   javalite
   [(μ h η e k)
    (begin 
      (printf "State:\n")
      (pretty-print (term (h η)))
      (printf "\n~a" (term e))
      (printf "\n~a" (term k))
      (flush-output))]))

;Select a random element from a list
(define (list-ref/random l)
  (list-ref l (random (length l))))

; Completely explores one path through reductions (so like apply-reduction-relation* but doesn't give all results from all paths)
; Note: apply-reduction-relation does one step, a-r-r* does all steps.
#;(define (apply-reduction-relation/random red t gc debug)
  (define tps (apply-reduction-relation red t))
  (if debug (begin (print-state t) (printf "\n\n")) #f)
  (if (empty? tps)
      (gc t) ;no more new states, so last state is the final state
      (apply-reduction-relation/random red (gc (list-ref/random tps)) gc debug)))

(define GC-FREQ 10)
(define (apply-reduction-relation/random red t gc [debug #f])
  (let loop ([t t] [i 0])
    (when debug 
      (print-state t))
    (define tps (apply-reduction-relation red t))
    (if (empty? tps)
        (gc t) ;no more new states, so last state is the final state
        (let ()
          (define n (list-ref/random tps))
          (loop
           (if (zero? i) (gc n) n)
           (modulo (add1 i) GC-FREQ))))))

(define (apply-reduction-relation/generator red initial-t visited? gc)
  (generator 
   ()
   (let loop ([before-gc-t initial-t])
     (define t (gc before-gc-t))
     ;(printf "~a\n\n" t)
     (unless (visited? t)
       (let ([tps (apply-reduction-relation red t)])
         (if (empty? tps)
             (yield t)
             (for-each loop tps)))))
   (yield #f)))

(define (make-hash-visited?)
  (define ht (make-hash))
  (λ (t)
    (if (hash-has-key? ht t)
        #t
        (begin0 #f
                (hash-set! ht t #t)))))

(define (make-null-visited?)
  (λ (t) #f))

(define get-e-from-state
  (term-match/single
   javalite
   [(μ h η e k)
    (term e)]))

(define (run-program prog gc debug)
  (get-e-from-state (apply-reduction-relation/random 
                     expr-reductions 
                     prog                      
                     gc
                     debug)))

(define (test-program/true prog gc debug)
  (test-predicate (procedure-rename (redex-match javalite true) 'true)
                  (run-program prog gc debug)))

(define (test-program/false prog gc debug)
  (test-predicate (redex-match javalite false)
                  (run-program prog gc debug)))

(define javalite-pp
  (term-match/single 
   javalite
   [(μ h η e k)
    (with-output-to-string
        (λ ()
          (pretty-display (term (h η e k)))))]))