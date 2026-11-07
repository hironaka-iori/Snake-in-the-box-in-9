# Round 182: completed native replay and the direction of an extension

The extended 012301 floor-14 certificate from round 181 now passes full native replay: 211,501 added clauses and 11,406,626 propagation hints, including the final empty clause. Together with the three replays from round 181, all four local floor-14 inputs have native refutations checked from their original clauses. Their combined totals are 650,902 added clauses and 33,809,191 propagation hints. The complete Lean contradiction proofs and geometric encoding interpretations remain separate, unfinished obligations.

## Every extension uses an unused coordinate

Consider the canonical six-edge segment

\[
0,1,3,7,15,14,12,
\]

with transition word 012301. Suppose it occurs in an induced path with at least seven edges. At least one endpoint of this segment has a path neighbour outside the segment, by the round-181 extension argument.

At the first endpoint, flipping coordinate 0 returns to the known neighbour 1. Flipping coordinate 1 gives vertex 2, which is adjacent to the internal vertex 3. Since 3 already has selected neighbours 1 and 7, selecting 2 would give degree three. Flipping coordinate 2 or 3 gives 4 or 8; these are the closing vertices already excluded in round 181. Therefore an external neighbour of 0 must be (2^a) for (4\le a<9).

At the other endpoint 12, coordinates 0, 1, 2 and 3 give 13, 14, 8 and 4. Vertex 14 is the known path neighbour. Vertex 13 is adjacent to 15, whose selected neighbours 7 and 14 already occupy its two possible path-neighbour positions. Vertices 4 and 8 are excluded closing vertices. Thus an external neighbour of 12 must be (12\mathbin{\oplus}2^a) for (4\le a<9).

Consequently every such window has a selected external neighbour obtained by flipping one of its five unused coordinates. This is a property of actual induced paths, independent of the share encoding. The statement, the degree exclusions and a canonical-window wrapper passed Lean in `lean/ExtensionDirection182.lean`, with four theorem dependency reports. Failed compiler and resource-stop records are preserved separately from the accepted receipt.

## A single representative extension

Permuting coordinates 4 through 8 fixes the original seven window vertices and can send any unused extension coordinate to coordinate 4. To interchange the two ends, first translate by exclusive-or with 12 and then interchange coordinates 0 with 1 and 2 with 3. This cube isometry sends the reversed window back to its canonical order, preserves the set of five share centres and maps a right extension (12\mathbin{\oplus}2^a) to a left extension (2^a), for (a\ge4).

Thus, up to cube isometry and reversal, it suffices to consider the selected extension vertex 16. The resulting eight-vertex path segment is

\[
16,0,1,3,7,15,14,12.
\]

Its transition word 4012301 becomes 0123412 after consistent relabelling. The physical five-centre share sum is invariant under this change of coordinates. This is a written symmetry reduction; the complete isometry transfer is not yet a Lean certificate.

## Strengthening the local target

The floor-15 query excludes share at most 14. Its streamed construction retains the saved radius-four input, removes the old total-share cap unit, adds a fifteenth share bit at each of the 35 centre-neighbour occurrences and a new cap-14 sum counter. Old cap-counter implications remain unconstrained above and can be satisfied without affecting the new bound. The two closing exclusions and necessary extension clause are retained for 012301.

For nonnegative integer shares (s_j),

\[
\sum_j\min\{s_j,15\}\le14
\quad\Longleftrightarrow\quad
\sum_j s_j\le14.
\]

Indeed, the left inequality excludes any (s_j\ge15), after which truncation changes no summand. The reverse implication follows term by term. `ShareTruncation182.lean` checks this fact for an arbitrary threshold and its cap-14 specialization, with two accepted theorem dependency reports. This arithmetic fact supports the changed cap; it does not replace the full Boolean-counter interpretation.

The first floor-15 search, allowing either extension endpoint, reached its 128 MiB raw-proof limit after approximately 87.48 seconds. It returned no accepted SAT or UNSAT conclusion. The representative-extension query selecting vertex 16 returned UNSAT in approximately 27.22 seconds. Its complete native replay passed: 100,151 added clauses and 4,348,019 propagation hints, including the final empty clause. The uncompressed proof is 37,061,374 bytes. The original input, its changed-cap semantics and the final proof are saved with hashes. The complete Lean and geometric interpretation of this stronger local Boolean result remains pending.

## The single-floor upgrade cannot close the current comparison

Consider the retained profile ((14,15,14,14)), ordered as 012034, 012301, 012340 and 012345. The saved nine-edge cycle has no 012301 edges, so its weight remains 4448. The saved eight-edge walk has two such edges; each gains one, changing its weight from 3356 to 3358. Reconstruction from the original scalar source rows verifies the vertices, directions, counts and new weights. No full new potential scan is asserted.

Every feasible mean (mu) and potential range (R) for this fixed graph must satisfy

\[
9\mu\le4448,\qquad R\ge8\mu-3358.
\]

For loss (L=1), the length comparison therefore has the lower bound

\[
\frac{1098595+8\mu+R}{4200+\mu}
\ge \frac{1095237+16\mu}{4200+\mu}
\ge 235+\frac{21}{42248}>235.
\]

The middle expression decreases with (mu), since (16\cdot4200<1095237). Its minimum over (0\le\mu\le4448/9) is the displayed value at (mu=4448/9). The loss-zero comparison is still larger. Three statements in `SingleFloorObstruction182.lean` check the denominator-cleared comparison, its strict consequence for a positive denominator and the endpoint arithmetic.

Thus strengthening 012301 alone to floor 15 cannot establish 234 through the current fixed-graph, zero-occurrence-credit mean-and-range argument in the remaining loss cases. This is a lower bound on the attainable comparison; no new potential attaining it has been constructed. It does not rule out stronger geometric information, a changed graph or other improved share floors. In particular, 012034 occurs six times on the unchanged cycle and remains a useful strengthening target.

## Consequences for the frontier

The new native replay completes the four floor-14 Boolean refutations. It does not close the Lean, count-restriction, exclusion or graph-coverage requirements. Under those retained premises the comparison remains

\[
42248m+45L\le9928364.
\]

Hence (L\ge2) would imply (m\le234), and any remaining hypothetical (m\ge235) case has (m=235), (L=0) or (L=1). A uniform floor-15 theorem would remove the loss premise from the current conditional comparison. No floor-15 result is established by a bounded search stop, and no new unconditional length bound follows here.

The next work is the Lean and geometric interpretation of the completed representative-extension certificate, followed by the remaining floor-15 targets, particularly 012034. The round-179 strict rational-share target (72/5) remains available for the small-loss cases. The current user instruction requires pausing after this round; no next round is authorized by this note.
