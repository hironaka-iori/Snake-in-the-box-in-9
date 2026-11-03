# Independent review of the count-free share13 input

Status: `PASS_INDEPENDENT_INPUT_CORE_AND_NATIVE_RUP_REVIEW`.

The exact prepared input was reconstructed as 10,616 variables and 88,038 clauses. Its bytes agree with both saved input copies. The ordinary base encoding accounts for 54,746 clauses on 421 vertices; an independently implemented, untagged base encoder produced the same clause sequence. Every saved variable meaning, counter, totalizer and clause tag agrees with the reconstruction.

All 10,078 core clauses were checked against their original clause IDs, preserving literal order and multiplicity. A separate positive-hint unit-propagation replay checked all 29,165 deductions and 1,699,457 hints and reached the empty clause. Every trimmed deduction is an unchanged line of the original native proof, in the same order. All saved input, generator, native executable, certificate and log hashes matched. No solver, Lean compiler or graph search was invoked by this review.

The input fixes the transition word `012034`, the seven vertices `[0,1,3,7,6,14,30]`, radius four, resolution 12, and share cap 12. All five singleton-square bounds are the full interval `[0,21]`; the only base counter is the endpoint budget of two. There are no parity, total-path-length, endpoint-location or extra cycle-cut restrictions. The ordinary base encoding does contain 2,844 four-cycle clauses and 10,152 six-cycle clauses. The core uses 142 of these ordinary cycle clauses. “No added cycle cuts” must not be read as absence of all cycle clauses.

The share encoding contains 35 centre-neighbor incidences over 32 distinct neighbor vertices. Each incidence has 28 candidate empty squares and 13 threshold literals, giving 980 empty-square variables and 455 cap literals. The repeated neighbor vertices contribute repeatedly, as required by a sum over centres. The audit independently reconstructed the totalizer clauses, all thresholds `ceil(t*d/12)`, the local square and neighbor sets, and the final cap clause. No incidence was deduplicated.

The remaining actual-snake interpretation needs the following arguments:

1. A fitting induced path satisfies the selected-window, degree, endpoint and ordinary four/six-cycle clauses. Radius-four boundary vertices have relaxed constraints; every vertex needed for the encoded square and neighbor counts lies in the ball.
2. For each internal centre, its two path neighbors are selected. The other seven neighbors are unselected, and each has at least one selected neighbor, namely the centre. Its denominator therefore lies between one and nine. Squares using the centre-neighbor direction contain that selected centre and contribute no empty square; the remaining 28 squares are exactly those encoded.
3. Under the proposed contradiction hypothesis that the five-centre integer share sum is at most 12, the threshold variables admit a satisfying assignment consistent with the one-direction totalizers and saturation at 13. This requires the precise integer-share definition and rounding argument. The totalizers should not be treated as unrestricted equivalences without proving the needed directions.
4. Coordinate relabelling and reversal must transport the local result to the intended actual windows. The reversed canonical word is `012342`; it is covered by reversing the path and the five-centre sum, not by silently identifying the two chronological words.

The native contradiction is established independently. Complete Lean replay and the actual-snake semantic bridge remain outside this review. No actual share lower bound or new global bound is asserted here. The saved case7302 completion record matches its earlier snapshot before and after this audit; the audit wrote no older files and does not claim a complete before/after comparison of that directory.

The reproducible checker is `audit/review-native.py`. Exact source hashes, full/core tag counts and replay statistics are recorded in `data/native-input-review.json`.
