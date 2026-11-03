# Independent review of the odd-pair-nine and six-count-twenty-five experiment

Result: `PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW`. The evaluator completed successfully in 159.125 seconds. The review checked its source, inheritance, saved input identities, and attaining cycles. It did not rerun the full graph or independently recompute every retained-edge inequality.

The finite graph contains 1,601,856 states and 4,661,773 retained edges. The added pair restriction removes 14,771 baseline edges; the six-count restriction removes another 6,570, for 21,341 additional removals. These counts are evaluator results, whose source and saved record were checked.

| Profile | Baseline minimum | New minimum | New attaining cycle | Baseline comparison | New comparison | Integer comparison |
| --- | --- | --- | --- | --- | --- | --- |
| `completed` | \(2915/6\) | \(488\) | 4 edges | \(1324108/5623\) | \(1103449/4688\) | 235, unchanged |
| `conditional_floor18` | \(496\) | \(496\) | 7 edges | \(551765/2348\) | \(551765/2348\) | 234, unchanged |

The first minimum increases by \(13/6\), with potential range changing from \(1730/3\) to \(585\). The second profile's minimum, potential range \(602\), and comparison are all unchanged. Neither integer comparison improves. These comparisons are conditional numerical consequences of the finite model; they do not establish bounds for arbitrary snakes.

## Count and credit rules

The evaluator's inherited prefix is exactly the milestone124 source prefix, apart from the output label. Its baseline assertions reproduce the milestone121 removal list and both complete weight-vector hashes before changing the model. The generator, generated evaluator, execution snapshot, run record and result record agree in their recorded source identities.

The pair test considers both placements and both orientations of canonical \(012032\). It rejects a pair only when both clipped symbols are below 6 and their sum is below 9. The second placement alone receives the corresponding credit. The independent arithmetic check covered all 441 actual pairs in \(\{1,\ldots,21\}^2\). The milestone130 parity receipt and its 20 pinned files were checked, and the actual theorem's fitting-window, canonical-shape and odd-length premises were inspected. Its conclusion applies to odd-length snakes, including length 235.

Symbol 6 retains its full interval \([6,21]\). Six-count deletion requires all six symbols to be exact and their sum to be below 25. Credit requires the first chronological symbol to be exact. Reversal changes shape recognition without moving this chronological guard. The independent check covered all 46,656 clipped six-tuples and checked that any permitted deficit can be paid from the five later count excesses. Old, pair and six-count credits are combined by their maximum, preserving the common budget of 24 per count. They are not added together.

Both profiles still inherit unproved count-sum assumptions. The profile named `completed` refers to its share-floor baseline; its full hypothesis set is not completely proved. The `conditional_floor18` profile also retains its additional share-floor assumptions. The \(0123104\) six-count floor 25 is hypothetical.

## Potential and cycle checks

The cycle search proposes a candidate. Exactness is then checked by integer relaxation on every retained edge, including edges outside the pruned cyclic subgraph. At convergence, the inequality

\[
dW(u,v)+\pi(u)-p-\pi(v)\geq 0
\]

implies that every directed cycle has mean at least \(p/d\). A closed cycle with equality on its edges attains that value. The evaluator checks both conditions and refuses a result if the relaxation does not converge within 1,500 iterations. The reviewed integer guard, \(1503B<2^{62}\), bounds each relaxation step and the later subtraction; at most 1,500 updates and the final slack expressions fit signed 64-bit arithmetic. The graph indices also fit their declared integer types.

The reviewer read each original graph-array member once, retained only the 29 selected edge rows, verified all six array hashes, and verified the sorted direction index. Each array contained 19,788,032 bytes. It reconstructed the two reported cycles' base weights, inherited bonuses, pair bonuses and six-count bonuses directly from those rows and the saved rule tables. All adjacency and exact mean checks passed. The compressed potentials were read and their full hashes, lengths, minima and ranges checked; every reported cycle edge has exactly zero potential slack. The two full all-edge checks were inspected in the evaluator and recorded successful result, without an independent second full-graph calculation.

The former eighteen-edge witness remains present and has recalculated mean \(3011/6\). This is correctly treated as a witness comparison, rather than the new minimum.

## Cycles that remain

The four-edge cycle of the `completed` profile has these exact pair matches:

| Source edge | Placement | Pair | Sum |
| --- | --- | --- | --- |
| 2222328 | 1 | \((4,5)\) | 9 |
| 147674 | 0 | \((4,5)\) | 9 |
| 2220858 | 1 | \((5,4)\) | 9 |
| 146782 | 0 | \((5,4)\) | 9 |

All six counts on each of these edges are exact. All four seven-direction windows have the same canonical shape \(0120324\) when reversal is included in canonicalization. They satisfy the added pair-nine condition with equality, receive no additional pair credit, and do not match the targeted six-shape \(0123104\).

The seven-edge cycle of the `conditional_floor18` profile has no pair-shape match in either placement. Its seven-direction shapes are \(0123045\), \(0123014\), and \(0123042\), with repetitions. It also avoids \(0123104\). Both cycles therefore receive zero added pair and six-count credit. Within this fixed finite model, raising only the floor for \(0123104\) cannot raise either minimum: the same attaining cycles remain with unchanged weights.

The monotonicity conclusion is exact within this finite model. Raising only the proposed floor from 25 upward increases some edge weights and deletes some edges, so the previous potential inequalities remain valid. The exhibited cycles avoid the targeted shape and keep their weights. They therefore continue attaining the same minima, 488 and 496.

Even an ideal potential range of zero would give the comparison values

\[
\frac{68929}{293}=235+\frac{74}{293}>235,
\qquad
\frac{137866}{587}=234+\frac{508}{587}>234.
\]

Consequently, strengthening only this pattern cannot reach the next integer comparison targets 234 and 233 through the same formula. This is an elementary finite-graph deduction; the native all-edge result and pending actual-snake assembly retain the scope stated above.

The baseline comparison, cycle observations and zero-range deduction were appended using the already source-checked saved rows. No original array was loaded a second time. The earlier review and checker hashes are retained in the final JSON as provenance.

## Scope and records

The remaining mathematical gap includes the inherited local hypotheses, the six-count premise, and the full graph-to-snake coverage and charge argument. The parity theorem alone does not close that gap. No new actual-snake upper bound is claimed.

The only preliminary inspection error was a call to an unavailable private NumPy header helper; the inspection was repeated using the public header reader. It changed no evaluator evidence or saved result. The graph run and review also emitted a Git commit-graph warning; the requested historical algorithm source was retrieved successfully and its hash matched. The review checker itself completed without a failed audit assertion.

`data/graph-review.json` records 79 file hashes, the bounded checks, all reviewed cycle details, and the scope limitations. Principal SHA256 values:

- Review JSON: `37991ffe6b084583bbd6c80f0c57c0c46c3a49d928cdc8e9a827571565fdd418`.
- Review checker: `cf1b54525ea274a2cf269d30832d1eadc6b81d1e1ee50d5757069e407cb4ea19`.
- Evaluator result: `157c1cd0751b487e220b954f441670839c50078167f54c83557f43f98fb8fd2d`.
- Evaluator run record: `e5b26d85b4655246f613c666570b2c359ea84abdafa767bee7884466382df172`.
