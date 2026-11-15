# Round 221: independent square-parity model audit

The baseline square-parity audit passed. All coordinate squares, all eight parity inequalities on each square, all inherited rows, the additional subset rows and both exact upper certificates were independently checked from the saved data. This review ran no optimizer, compiler, search worker or software tests.

## Validity and complete square coverage

For a Boolean vertex selection with edge products \(y_{uv}=x_ux_v\), write \(\delta_{uv}=x_u+x_v-2y_{uv}\). This is the indicator that the two endpoints differ. The disagreement pattern around every cycle has even cardinality. For any odd subset \(F\) of a square's four edges, the disagreement pattern differs from \(F\) on at least one edge. Consequently

\[
\sum_{e\in F}\delta_e-\sum_{e\notin F}\delta_e\le |F|-1.
\]

There are eight such odd subsets. These inequalities hold for every Boolean selection and therefore every actual partner; they do not require an additional path assumption.

The audit directly enumerated all coordinate two-faces contained in the frozen allowed vertex sets, independently of the producer's saved cycle list. It found 156 squares for root 0 and 154 for root 78. Those sets exactly equal the saved four-cycle inventory. Every listed cycle has four distinct adjacent vertices, and each square receives all eight odd edge masks exactly once.

Each parity row was reconstructed by substituting the displayed disagreement formula, combining coefficients, and matching its variable indices, name, right-hand side and row position. This verifies 1,248 and 1,232 added square rows. The round-220 model prefixes and 25 inherited subset records are unchanged. Root 0 adds no further subset row; root 78 adds four. Every additional subset/vertex key and row was reconstructed as
\(\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v\), with \(v\in U\).

The resulting models contain 574 variables each and 3,118 or 3,101 rows. The source's rounded min-cut search only discovers candidates. Row validity is independent of the floating discovery calculation; absence of further detected violations is not an exact completeness certificate for the subset family.

## Exact upper certificates

| Root | Exact certified upper bound | Numerical reported objective |
|---:|---:|---:|
| 0 | \(48000361/500000=96.000722\) | \(96.0006107671\) |
| 78 | \(95779317/10^6=95.779317\) | \(95.7792146824\) |

The audit recomputed every signed equality weight, nonnegative inequality weight, coefficient residual, positive residual contribution and final rational bound. For variables in the interval from 0 to 1, summing the weighted rows and bounding each residual contribution by its positive part proves these upper bounds without numerical dual feasibility or optimality assumptions.

Neither upper certificate is below 94. With integral even cardinality, they imply at most 96 selected vertices for a Boolean odd-edge partner at root 0 and 94 at root 78. These are restrictions on the fixed-parent model, not global snake bounds.

## Effect on the preceding points

Every round-220 source point was matched to the frozen audit before evaluation. The exact numbers of violated new square rows are:

| Root | Original rational point | Cardinality-94 mixture |
|---:|---:|---:|
| 0 | 56 | 49 |
| 78 | 51 | 44 |

Thus the square constraints remove the previous fractional examples. This baseline audit alone does not establish whether replacement fractional points exist or satisfy all subset inequalities. Later rational data require their own audit.

## Provenance and limitations

The generator, generated source and wrapper were inspected. The saved execution is terminal with exit 0 and no stop, elapsed 3.141 seconds, maximum sampled private memory 32,104,448 bytes and minimum sampled free memory 1,426,313,216 bytes. Source/input pins, summary and stream hashes, iteration counts and saved resource conditions match. Resource maxima are sampled observations.

The initial reviewer execution completed its mathematical checks but failed while formatting a predecessor path outside this milestone. The path labels were changed to absolute paths, and the complete audit then passed. This was a reviewer report-serialization error; no producer source or evidence was modified. The receipt records the repair.

No exact LP optimality, all-subset closure, Boolean partner, global length bound or concrete Lean assembly is claimed here. Generic Boolean parity and actual-path proofs remain separate from this native exact-array audit. The complete source and evidence hashes are in `data/square-audit.json`.

These baseline files are frozen. Rational-point and other subsequent checks belong to separate addenda.
