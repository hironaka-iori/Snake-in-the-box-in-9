# Independent bounded review of the share18 graph result

Status: `PASS_BOUNDED_GRAPH_CYCLE_REVIEW`.

The saved eleven-edge cycle and its reported comparison are correct under the recorded graph hypotheses. In the same zero-credit model, increasing only the canonical `012034` suffix share floor cannot bring the comparison below 235. This conclusion follows from the saved cycle alone and does not require accepting the producer's global minimum claim.

The evaluator was compared with the frozen milestone142 evaluator. Its literal source transformations were independently reproduced. The changes affecting the model are exactly the addition of the `012034` floor18 after predecessor reconstruction and the switch from weights scaled by 12 with occurrence credit to unscaled weights with zero credit. Historical predecessor checks remain unchanged. The current removed-edge file is byte-identical to milestone142; no additional count-free floor or new edge deletion was introduced.

All six original source-array payload hashes were checked by reading bounded one-megabyte chunks. Only the eleven selected rows were retained. From those rows, the direction words, clipped count digits, original weights, completed share floors, inherited rule bonuses, pair and six-count bonuses, shared maximum, occurrence indicators and new share18 contribution were recomputed. Every field agrees with the saved result, and every cycle edge remains in the recorded graph.

| Original edge | Canonical suffix, allowing reversal | Weight | Occurrence event |
| ---: | --- | ---: | --- |
| 2222339 | `012032` | 360 | Yes |
| 147722 | `012314` | 496 | No |
| 2221095 | `012032` | 480 | Yes |
| 147978 | `012314` | 496 | No |
| 2208886 | `012031` | 496 | No |
| 118572 | `012031` | 376 | No |
| 2140364 | `012314` | 616 | No |
| 2534 | `012032` | 487 | Yes |
| 1107797 | `012314` | 496 | No |
| 2220859 | `012032` | 480 | Yes |
| 146785 | `012314` | 616 | No |

Every target vertex equals the next edge's source vertex, including the closing edge. The weights sum to 5399, giving mean \(5399/11\). Neither chronological orientation of any suffix has canonical shape `012034`, so all eleven added share-floor contributions are zero. There are four occurrence events; this is not a zero-event cycle. Digits equal to six continue to represent the interval `[6,21]` in the local rule tests.

The saved potential contains 1,601,856 signed 64-bit entries. Its uncompressed hash matches the result, its minimum is zero, and its maximum is 6523. With denominator 11, the potential range is \(6523/11=593\). Each cycle edge has exactly zero slack in

\[
11w(u,v)+h(u)-5399-h(v)\geq0.
\]

The reported 29 iterations are preserved as a computation statistic; they do not establish that the range is optimal. Exact arithmetic gives

\[
\frac{1098960\cdot11+8\cdot5399+6523}{4200\cdot11+5399}
=\frac{12138275}{51599}
=235+\frac{12510}{51599}.
\]

For any value of the `012034` floor, these cycle weights remain unchanged as long as the other weights and retained edges are fixed and the occurrence credit stays zero. Any feasible graph comparison mean therefore satisfies \(0\leq\mu\leq5399/11\). Since the potential range is nonnegative and the zero-range expression decreases with \(\mu\),

\[
\frac{1098960+8\mu+R}{4200+\mu}
\geq
\frac{1098960+8(5399/11)}{4200+5399/11}
=\frac{12131752}{51599}
=235+\frac{5987}{51599}>235.
\]

Thus arbitrarily strengthening only this suffix share floor cannot reach the next integer target through the current zero-credit comparison. Changing the occurrence credit changes four cycle weights, so that different model is outside this obstruction.

This audit independently checked the source transformations, source-array hashes, selected rows, closed cycle, saved potential hash and range, cycle slacks and rational arithmetic. It did not repeat all-edge potential checks, reconstruct the full new weight-array hash, run a graph optimizer or prove the potential range optimal. The producer's all-edge certificate is still the evidence for the exact full-graph minimum.

The inherited count-sum assumptions, hypothetical six-count floor25, odd-length pair restriction, pending actual share18 theorem and full graph-to-snake assembly remain separate. This is a finite-graph comparison limitation, not a global impossibility theorem for snakes. The additional milestone141 profile is unchanged and is not replaced by this result.

Exact pins and row data are saved in `data/graph-review.json`. The reproducible bounded checker is `audit/review-graph.py`. No Lean compiler, solver or graph optimizer was invoked.
