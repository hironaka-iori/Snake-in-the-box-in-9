# Saved-cycle obstruction including the potential range

Status: `PASS_SAVED_CYCLE_AND_WALK_RANGE_REVIEW`.

The nine saved edges from milestone142 were checked against the pinned saved-row review. Their adjacency closes the cycle. Direction normalization, the chronological five-count slices and the suffix occurrence predicate were recomputed from the saved rows. All nine occurrence indicators are false. This review uses the earlier independently streamed source-row check as provenance; it does not reload the source graph or repeat an all-edge scan.

Increasing only the count-free share floor for canonical `012034` to 14 gives the following unscaled weights, in saved cycle order:

\[
(614,494,376,734,374,492,614,374,376).
\]

Their sum is 4448. The five consecutive edges at row indices 4 through 8 have weights

\[
(374,492,614,374,376),
\qquad 374+492+614+374+376=2230.
\]

The evaluator uses the potential inequality

\[
w(u,v)+h(u)-h(v)-\mu\geq 0,
\qquad R=\max h-\min h.
\]

Summing around the nine-cycle gives \(\mu\leq 4448/9\). Summing along the selected five-edge walk gives

\[
R\geq h(u_{4})-h(v_{8})\geq 5\mu-2230.
\]

These two inequalities hold uniformly when the `012034` floor is at most 14: lowering this floor can only decrease the cycle and walk weights. Adding any uniform credit on the same suffix event leaves these nine edges unchanged because every event indicator is zero. This statement requires the same retained edges and all other weights and bonuses to remain fixed.

Write the occurrence cost as \(BC\geq0\). For \(\mu\geq0\), the comparison then satisfies

\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\geq
\frac{1096730+13\mu}{4200+\mu}.
\]

The last expression decreases with \(\mu\): its derivative has numerator \(-1042130\) and positive denominator \((4200+\mu)^2\). Consequently,

\[
\frac{1098960+8\mu+BC+R}{4200+\mu}
\geq
\frac{4964197}{21124}
=235+\frac{57}{21124}>235.
\]

Thus floors 13 and 14 cannot reach a comparison below 235 through this fixed model, even with zero occurrence cost. The previous floor13 calculation correctly removed the zero-range obstruction; the five-edge walk shows that zero range is unavailable at the relevant mean.

| Share floor | Cycle total | Five-edge walk total | Forced range at the cycle mean | Comparison with zero occurrence cost |
| --- | ---: | ---: | ---: | ---: |
| 13 | 4442 | 2227 | \(2167/9\) | \(235+1473/42242\) |
| 14 | 4448 | 2230 | \(2170/9\) | \(235+57/21124\) |
| 15 | 4454 | 2233 | \(2173/9\) | \(235-1245/42254\) |

For these three floors, the range forced by the chosen walk at the cycle mean also equals the largest minus smallest cumulative reduced weight around the entire saved cycle. Floor 15 is therefore the first integer floor not excluded by this cycle-and-walk test. Other cycles, other paths, positive occurrence cost, and the inherited local hypotheses may still obstruct the desired comparison. The existing additional profile continues to require floor 18. No new share theorem, graph minimum or global snake bound follows from this audit.

Exact row data, floor comparisons from 0 through 18, and current source hashes are saved in `data/range-review.json`. No solver, Lean compiler or graph search was invoked.
