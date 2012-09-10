#lang racket
(require redex/reduction-semantics
         redex/pict
         "javalite.rkt")

(render-language javalite-surface "javalite-surface.eps")
(render-language javalite "javalite-machine.eps")
(render-reduction-relation expr-reductions "javalite-reductions.eps")

(render-reduction-relation-rules '("Variable access"))
(render-reduction-relation expr-reductions "rules/variable-access.eps")

(render-reduction-relation-rules '("new"))
(render-reduction-relation expr-reductions "rules/new.eps")

(render-reduction-relation-rules '("field access - object eval"))
(render-reduction-relation expr-reductions "rules/field-access-object-eval.eps")

(render-reduction-relation-rules '("field access"))
(render-reduction-relation expr-reductions "rules/field-access.eps")

(render-reduction-relation-rules '("method invocation - object eval"))
(render-reduction-relation expr-reductions "rules/method-invocation-object-eval.eps")

(render-reduction-relation-rules '("method invocation - arg0 eval"))
(render-reduction-relation expr-reductions "rules/method-invocation-arg0-eval.eps")

(render-reduction-relation-rules '("method invocation - argi eval"))
(render-reduction-relation expr-reductions "rules/method-invocation-argi-eval.eps")

(render-reduction-relation-rules '("method invocation - no args"))
(render-reduction-relation expr-reductions "rules/method-invocation-no-args.eps")

(render-reduction-relation-rules '("method invocation - args"))
(render-reduction-relation expr-reductions "rules/method-invocation-args.eps")

(render-reduction-relation-rules '("raw method invocation"))
(render-reduction-relation expr-reductions "rules/method-invocation-raw.eps")

(render-reduction-relation-rules '("equals - l-operand eval"))
(render-reduction-relation expr-reductions "rules/equals-l-operand-eval.eps")

(render-reduction-relation-rules '("equals - r-operand eval"))
(render-reduction-relation expr-reductions "rules/equals-r-operand-eval.eps")

(render-reduction-relation-rules '("equals"))
(render-reduction-relation expr-reductions "rules/equals.eps")

(render-reduction-relation-rules '("typecast - object eval"))
(render-reduction-relation expr-reductions "rules/typecast-object-eval.eps")

(render-reduction-relation-rules '("typecast"))
(render-reduction-relation expr-reductions "rules/typecast.eps")

(render-reduction-relation-rules '("instanceof - object eval"))
(render-reduction-relation expr-reductions "rules/instanceof-object-eval.eps")

(render-reduction-relation-rules '("instanceof"))
(render-reduction-relation expr-reductions "rules/instanceof.eps")

(render-reduction-relation-rules '("assign -- object eval"))
(render-reduction-relation expr-reductions "rules/assign-object-eval.eps")

(render-reduction-relation-rules '("assign"))
(render-reduction-relation expr-reductions "rules/assign.eps")

(render-reduction-relation-rules '("assign field -- object eval"))
(render-reduction-relation expr-reductions "rules/assign-field-object-eval.eps")

(render-reduction-relation-rules '("assign field"))
(render-reduction-relation expr-reductions "rules/assign-field.eps")

(render-reduction-relation-rules '("if-then-else -- object eval"))
(render-reduction-relation expr-reductions "rules/if-then-else-object-eval.eps")

(render-reduction-relation-rules '("if-then-else"))
(render-reduction-relation expr-reductions "rules/if-then-else.eps")

(render-reduction-relation-rules '("variable declaration -- object eval"))
(render-reduction-relation expr-reductions "rules/variable-declaration-object-eval.eps")

(render-reduction-relation-rules '("variable declaration"))
(render-reduction-relation expr-reductions "rules/variable-declaration.eps")

(render-reduction-relation-rules '("begin -- empty expression list"))
(render-reduction-relation expr-reductions "rules/begin-empty-expression-list.eps")

(render-reduction-relation-rules '("begin -- e_0 evaluation"))
(render-reduction-relation expr-reductions "rules/begin-e_0-evaluation.eps")

(render-reduction-relation-rules '("begin -- e_i evaluation"))
(render-reduction-relation expr-reductions "rules/begin-e_i-evaluation.eps")

(render-reduction-relation-rules '("begin -- complete"))
(render-reduction-relation expr-reductions "rules/begin-complete.eps")

(render-reduction-relation-rules '("pop η"))
(render-reduction-relation expr-reductions "rules/pop.eps")

(render-metafunctions length-bug
                      default-value
                      default-value*
                      h-max
                      h-malloc
                      h-malloc-n-helper
                      h-malloc-n
                      internal-h-malloc-n*
                      h-malloc-n*
                      storelike-lookup
                      h-lookup
                      h-extend*
                      η-lookup
                      η-extend*
                      restricted-field-lookup
                      field-lookup
                      restrict-object
                      class-name
                      parent-name
                      field-list
                      class-list-extend
                      class-lookup
                      class-list-from-object
                      class-parents+self
                      field-lists-extend
                      #:file "javalite-metafunctions-p1.eps")

(render-metafunctions fields-parents+self
                      method-name
                      method-expression
                      method-args
                      method-lookup
                      cast
                      instanceof*
                      inject
                      inject/with-state
                      #:file "javalite-metafunctions-p2.eps")
