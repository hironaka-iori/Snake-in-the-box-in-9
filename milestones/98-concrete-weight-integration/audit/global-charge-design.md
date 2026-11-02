# Actual total-weight charge budget

Completion update: the module passed the parent compiler check. The source
hashes below record the initial design; successful compiler receipts preserve
the final checked bytes and any small proof repairs.

Status: complete source written in `lean/GlobalCharge98.lean`, awaiting the parent's sequential Lean check. This subtask has not launched a compiler.

The module imports `CombinedWeights98` and `UpperBound247`. It avoids the old `ExtendedBudget` and `BoundaryCharge` import environments. The only copied argument is the generic arithmetic proof of `BoundaryCharge67.discarded_counts`, placed in the fresh namespace `Snake9.GlobalCharge98`. It is supplied with actual-snake hypotheses proved inside the new module.

## Main statement

Let $p$ be a snake with $m\ge9$ edges and let $F$ be a numerical floor lookup. Assume precisely the per-window floor bound

$$
F(\operatorname{directionId}(p,r))
\le \sum_{i=0}^{4}\operatorname{coreShare}(12,p,r+i+4)
\qquad(r+9\le m).
$$

Write $w_r$ for the existing `Weights98.weight` evaluated at the actual history, direction and six-count code, with floor $F$. The proposed theorem `actual_total_weight_budget` concludes

$$
\sum_{r=0}^{m-9}w_r+4200m\le1098960.
$$

Its Lean statement uses `Finset.range (m-8)`. It has no endpoint, incidence, graph-coverage or reference-catalogue premise. The endpoint and charge facts are discharged by existing actual-snake theorems.

`completed_total_weight_budget` supplies the floor bound using `CountFree98.actual_completed_credit`. It therefore has only the snake and $m\ge9$ as explicit parameters. A conditional profile can use the same main theorem after supplying its five local-refutation premises through `actual_conditional_credit`.

## Proof accounting

Put

$$
B=\sum_{r=0}^{m-9}\alpha_{r+8},\qquad
T=\operatorname{totalSingleton}(p),\qquad
S=\sum_{k=0}^{m}\operatorname{coreShare}(12,p,k).
$$

The entering count indices are $8,\ldots,m-1$. The discarded indices $0,\ldots,7,m$ contribute at least21:

- The two endpoints contribute at least4 each, using `endpoint_alpha_ge_four`.
- The internal pairs $(1,2),(3,4),(5,6)$ contribute at least4 each, using `adjacent_internal_alpha_sum_ge_four`.
- Index7 contributes at least1, using `core_count_positive`.

`localAlpha_eq_coreAlpha` transfers the geometric count facts to the representation used by the weights. `core_count_total` identifies the complete core-count sum with $T$. Thus `actual_entering_count_budget` gives $B+21\le T$.

Let $L$ be the sum of the five-centre share sums over the actual graph windows. The checked `shifted_prefix_sum_le` compares each of the five shifted sums with the whole path. Summing those inequalities gives $L\le5S$, implemented as `actual_share_overlap`. The largest charged centre is $m-1$, so all indices used are within the path.

`Weights98.actual_weight_bound` gives $W\le120B+L$, where $W=\sum_r w_r$. Consequently,

$$
W+2520\le5(24T+S).
$$

The existing `CountFreeBridge.core_share12_charge_le` gives

$$
24T+S+840(m+1)\le221136.
$$

Multiplying by5 and combining the inequalities yields

$$
W+4200(m+1)+2520\le1105680,
$$

which is the stated budget. The constant uses the21-count boundary saving. The older15-count estimate would produce a weaker constant and is not used.

## Audit declarations and limits

The source requests six axiom reports:

- `discarded_counts`
- `core_count_total`
- `actual_entering_count_budget`
- `actual_share_overlap`
- `actual_total_weight_budget`
- `completed_total_weight_budget`

All are in `Snake9.GlobalCharge98`. No new finite geometry search, graph enumeration, or potential check is introduced. The exact definition of `Weights98.weight` remains owned by the parent.

The result is an upper budget for the actual total weight. A matching lower bound from a graph potential, its range, and the actual graph-key walk are separate inputs to any numerical snake-length conclusion. The two reference-catalogue premises remain relevant to that graph-membership stage; they are unnecessary for the actual-snake charge budget itself.

## Inspected source pins

| Source | SHA-256 |
|---|---|
|98 `lean/GlobalCharge98.lean`|`9a93b609aeac7484879205f544634fc3dccc4aa67ccf569b801957e939e93fe2`|
|98 `lean/CombinedWeights98.lean`|`3cf85803aa0ce0112186bbb47b3c65e28dd02ee66ee9b91f189c677a3f9e9c36`|
|67 `lean/BoundaryCharge.lean`|`52d8e21be70a6ea34d98f140eef9e123b41b532f34dbe838cdea82f94991e52e`|
|59 `lean/ExtendedBudget.lean`|`002d6762831b031181307f7e33f85d315dd4eaab7e41618939d916a30c17e206`|
|73 `bridge/lean/CoreShareBudget.lean`|`81ccb6a86bb022c4acc6e5a15f09e5960caa5e0256ea4c6771830f9920344f0a`|
|73 `bridge/lean/FiveCentreOverlap.lean`|`c52008307937d17905342de3d7a7f7f6515243f7ec225d0ca2cb1fc1810e54a8`|
|78 `lean/CountGeometry.lean`|`ab0ecb37c727680f676394c895cd09a7f26cd7315ee5286d8893d480a7937747`|
|Verification source `UpperBound247.lean`|`10de776e354f113dab257cadb7dd43e7e55d54e950e386a44d5224403070258f`|
|Verification source `Aggregate247.lean`|`c33e90119aadb9f4c029841fe1c92b378b6048e0c4ea44d2fcb0ba167503d368`|

The two verification sources are under `work/spectral/.verification/strengthened-n8g3mwjy/`. Their objects resolve in the existing milestone98 environment. The parent owns the new compilation receipts and any subsequent source-repair hashes.
