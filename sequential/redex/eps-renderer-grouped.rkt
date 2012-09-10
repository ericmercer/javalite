#lang racket
(require redex/reduction-semantics
         redex/pict
         "javalite.rkt")

(render-language javalite-surface "javalite-surface.eps")
(render-language javalite "javalite-machine.eps")

(render-reduction-relation expr-reductions "javalite-reductions.eps")

(rule-pict-style 'compact-vertical)
(render-reduction-relation-rules '("variable access"))
(render-reduction-relation expr-reductions "grouped-rules/variable-access.eps")

(render-reduction-relation-rules '("new"))
(render-reduction-relation expr-reductions "grouped-rules/new.eps")

(render-reduction-relation-rules '("field access - object eval" "field access"))
(render-reduction-relation expr-reductions "grouped-rules/field-access.eps")

(render-reduction-relation-rules '("method invocation - object eval" "method invocation - arg0 eval" "method invocation - argi eval" "method invocation - no args" "method invocation - args" "raw method invocation"))
(render-reduction-relation expr-reductions "grouped-rules/method-invocation.eps")

(render-reduction-relation-rules '("method invocation - object eval" "method invocation - arg0 eval" "method invocation - argi eval" "method invocation - no args" "method invocation - args"))
(render-reduction-relation expr-reductions "grouped-rules/method-invocation-minus-raw.eps")

(render-reduction-relation-rules '("raw method invocation"))
(render-reduction-relation expr-reductions "grouped-rules/method-invocation-raw.eps")

(render-reduction-relation-rules '("equals - l-operand eval" "equals - r-operand eval" "equals"))
(render-reduction-relation expr-reductions "grouped-rules/equals.eps")

(render-reduction-relation-rules '("typecast - object eval" "typecast"))
(render-reduction-relation expr-reductions "grouped-rules/typecast.eps")

(render-reduction-relation-rules '("instanceof - object eval" "instanceof"))
(render-reduction-relation expr-reductions "grouped-rules/instanceof.eps")

(render-reduction-relation-rules '("assign -- object eval" "assign"))
(render-reduction-relation expr-reductions "grouped-rules/assign.eps")

(render-reduction-relation-rules '("assign field -- object eval" "assign field"))
(render-reduction-relation expr-reductions "grouped-rules/assign-field.eps")

(render-reduction-relation-rules '("if-then-else -- object eval" "if-then-else"))
(render-reduction-relation expr-reductions "grouped-rules/if-then-else.eps")

(render-reduction-relation-rules '("variable declaration -- object eval" "variable declaration"))
(render-reduction-relation expr-reductions "grouped-rules/variable-declaration.eps")

(render-reduction-relation-rules '("begin -- empty expression list" "begin -- e_0 evaluation" "begin -- e_i evaluation" "begin -- complete"))
(render-reduction-relation expr-reductions "grouped-rules/begin.eps")

(render-reduction-relation-rules '("pop η"))
(render-reduction-relation expr-reductions "grouped-rules/pop.eps")

#;(render-metafunctions get-length
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

#;(render-metafunctions fields-parents+self
                      method-name
                      method-expression
                      method-args
                      method-lookup
                      cast
                      instanceof*
                      inject
                      inject/with-state
                      #:file "javalite-metafunctions-p2.eps")
