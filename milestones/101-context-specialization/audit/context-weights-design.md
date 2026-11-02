# Context weight specialization

Initial delegated design note, followed by the parent compilation. The generic module passed Lean with three clean axiom audits. Current concrete coverage is recorded separately in `data/proof-summary.json`.

## Executable interface

The module imports `WeightSpecialization100` and adds one executable definition, `Snake9.ContextWeights101.emittedCredit`. It accepts the existing `List Rule` and a natural count code. For each rule it takes the maximum of the geometric credit and the strong credit gated by the original `numericCapsTest`, then takes the maximum with the remaining list. The empty list contributes zero.

This evaluator reads only the geometric credit, caps and strong credit. It does not repeat the context's signature-emission test. The original evaluator already leaves the compatible-word proofs to its separate semantic interface; no executable compatible-word test is removed here.

## Proof declarations

Three declarations have axiom-print commands:

1. `historyCredit_eq_emitted rules q di code hemit` equates the original history evaluator with the new evaluator when every listed rule emits in the specified context. The proof is a list induction and preserves both the count-cap test and the maximum operation.
2. `historyCredit_eq_selected selected q di code hselected` applies this equality to the complete concrete catalogue. Its explicit premise states that `selected` equals the catalogue filtered by the original suffix-emission predicate. This exact list equality preserves order and multiplicity. The existing filtering theorem supplies equality to the original catalogue evaluator; membership in the filter supplies each emission premise.
3. `weight_eq_context floor q di selected G F C hselected hG hF hC code` gives the exact original weight using the selected list and supplied fixed lookup results.

The final theorem's lookup premises are:

$$
G=g_d,\qquad F=\mathrm{floor}(d),\qquad
\forall c,\ b(d,c)=C(c),
$$

where $g_d$ is the existing geometric lookup and $b$ is the existing conditioned-credit function. Its conclusion is

$$
w_{\mathrm{floor}}(q,d,c)
=120(c\bmod6+1)
+\max\!\left(
\max\!\left(G,\mathrm{emittedCredit}(\mathrm{selected},c)\right),
\max\!\left(C(c),F\right)
\right).
$$

The selected-list equality and both lookup equalities have the exact orientations requested by the caller. The conditioned-credit premise quantifies over every natural code. The resulting weight equality likewise holds for every natural code and requires no code-range, direction-range or history-range premise.

## Integration and limitations

Each concrete context can establish its selected list, geometric lookup, floor lookup and conditioned-credit expression once. The resulting pointwise equality can then transfer a certificate checked with the simplified expression to the original weight. This module adds no context table, new rule datatype, graph definition, endpoint formula or potential definition.

No rule-validity or local-refutation premise is needed to equate these executable evaluators. The existing semantic premises remain necessary when the original weight is used to bound actual snake shares, including the pending local refutations for conditional floors. Symbol6 keeps its existing saturated-count interpretation because the original cap test is reused without modification.

The imported milestone100 weight-specialization receipt records a successful13-audit check. The milestone101 generic source subsequently passed compilation and all three axiom audits. Concrete context equalities and finite potential checks have separate receipts. This evaluator argument alone asserts no runtime improvement or numerical upper-bound improvement.
