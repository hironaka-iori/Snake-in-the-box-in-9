# Independent review of the retuned share18 graph

Status: `PASS_BOUNDED_RETUNED_CYCLE_REVIEW`.

The saved fourteen-edge cycle is correct and remains unchanged under any alteration of only the canonical `012034` suffix share floor and the uniform occurrence credit on the existing event. It contains neither a matching suffix nor an occurrence event. Consequently these two parameters alone cannot bring the current comparison below 235, even with zero cost and zero potential range.

The evaluator's literal transformations from the previously audited zero-credit evaluator were independently reproduced. The new weight is

\[
W=36(w+\text{shared bonus})+601\,\mathbf{1}_{\text{event}},
\]

with the same share18 addition, exclusions and inherited hypotheses. The removal files remain byte-identical to milestone142. The saved script, run, source pins and potential hash match. The field `occurrence_credit_scaled` is the global coefficient 601; the actual applied increment is that coefficient multiplied by the event indicator. It is zero on every row of this cycle. All saved bytes were preserved.

All six original source-array payload hashes were checked in one-megabyte chunks, retaining only the fourteen selected rows. Direction normalization in both orientations, clipped count intervals, completed share floors, rule bonuses, pair/six-count bonuses, their shared maximum and occurrence predicates were recomputed. Every saved row and weight agrees with this reconstruction, and every edge remains in the recorded graph.

| Original edge | Canonical suffix, allowing reversal | Unscaled weight |
| ---: | --- | ---: |
| 973890 | `012304` | 256 |
| 1205785 | `012301` | 246 |
| 2552723 | `012304` | 736 |
| 3050240 | `012304` | 496 |
| 991817 | `012301` | 371 |
| 1272513 | `012304` | 736 |
| 3029988 | `012340` | 364 |
| 976241 | `012304` | 496 |
| 1202057 | `012301` | 486 |
| 2553325 | `012304` | 376 |
| 3052648 | `012304` | 736 |
| 987229 | `012301` | 371 |
| 1275764 | `012304` | 496 |
| 3031022 | `012340` | 724 |

The canonical suffix multiplicities are `012304`: eight, `012301`: four, and `012340`: two. No suffix has shape `012034` in either orientation; this was checked directly rather than inferred from its zero recorded bonus. The forward forms `012341` are reversed instances of `012304`. All fourteen occurrence indicators are false.

The edges connect consecutively and close. Their unscaled weights sum to 6890, so the mean is \(6890/14=3445/7\). The scaled weights sum to 248040 and have mean \(124020/7\). The saved potential has 1,601,856 entries, minimum zero and maximum 153216, giving actual range

\[
\frac{153216}{36\cdot7}=608.
\]

All fourteen scaled cycle slacks are exactly zero. The recorded 35 iterations are a computation statistic, with no claim of optimal potential range. The retuned comparison is

\[
\frac{1098960\cdot36\cdot7+8\cdot124020+24\cdot601\cdot7+153216}
     {4200\cdot36\cdot7+124020}
=\frac{23182022}{98535}
=235+\frac{26297}{98535}.
\]

With the retuned occurrence cost retained but range zero, the comparison is \(23169254/98535\). This differs from the zero-cost, zero-range value used for the parameter-independent obstruction below.

Fix the retained edges and all other completed-profile weights. Since this cycle has no relevant suffix and no event, any value of the `012034` floor and any uniform occurrence credit leave its unscaled mean unchanged. Thus an admissible comparison mean satisfies \(0\leq\mu\leq3445/7\). For any nonnegative occurrence cost \(BC\) and range \(R\),

\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\geq
\frac{1098960+8(3445/7)}{4200+3445/7}
=\frac{1544056}{6569}
=235+\frac{341}{6569}>235.
\]

The inequality uses monotonic decrease of the zero-cost, zero-range expression with respect to \(\mu\). It rules out reaching the next integer target through these two parameters in this fixed model. Improving a share floor on a shape absent from the cycle cannot change this obstruction. An additional share improvement must affect `012304`, `012301` or `012340`, or another justified change must alter the cycle or its weights.

This review checked selected source rows, cycle connectivity, exact weights and arithmetic, potential hash and range, and cycle slacks. Full weight-array reconstruction, all-edge potential inequalities and exact full-graph minimality remain producer checks. The actual share18 theorem, inherited count-sum and hypothetical six-count assumptions, odd-length restriction and full graph-to-snake assembly remain separate. The conclusion is a limitation of this graph comparison, not a global impossibility theorem for snakes.

No optimizer, solver or Lean compiler was invoked. Exact source pins and reconstructed rows are saved in `data/retuned-review.json`; the bounded checker is `audit/review-retuned.py`.
