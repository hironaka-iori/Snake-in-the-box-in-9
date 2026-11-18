# Next step after explicit resumption

The user requested a pause after Round 240. Do not execute the work below until she explicitly resumes the goal.

## Preferred mathematical route

Continue the structural reconstruction question for six through eight affected neighbour counts, using connected generator-coordinate configurations and the actual amplitude bound \(|w_i|\le9\).

The Round 240 result gives a useful preliminary reduction. Split a nonzero selection difference \(f\) into its even and odd restrictions. Their neighbour-sum supports are disjoint, and every nonzero restriction requires at least six affected counts by five-count recovery. If the total support has at most eight positions, only one restriction can be nonzero. Therefore a possible counterexample in the remaining range can be sought on one parity side.

Every such counterexample must contain a distance-eight pair, by the conditional eight-count theorem. Its distance-eight graph is bipartite. For each connected component with \(k\le8\) positions, a spanning tree supplies at most \(k-1\) independent generator labels. Work with this concrete coordinate representation; the matrix coefficients are determined by the number \(t\) of differing generator coordinates:

\[
d_{Q_9}=t\quad\text{if }t\text{ is even},\qquad
d_{Q_9}=9-t\quad\text{if }t\text{ is odd}.
\]

This preserves the geometry needed for the antipodal equations. The entire-support star family and the full three-dimensional generator cube are already settled by the written arguments in STRUCTURAL_NOTE.md.

The first useful task is to identify remaining connected configurations at six positions and derive their bounded integer consequences. Use equation differences, repeated-row symmetries, or character sums when the configuration has the required symmetry. Keep any claim restricted to the configurations actually covered.

## Conditions that must remain in the argument

For actual selection differences, the unknown affected counts satisfy

\[
Hw=315s,\qquad s_i\in\{-1,0,1\},\qquad |w_i|\le9.
\]

The bound on \(w\) is essential for a method intended to reach eight positions. The explicit generator cube has nonzero integer solutions of amplitude 21. Thus the unrestricted-integer conclusion used successfully for five positions cannot simply be extrapolated.

Disconnected components must be considered together. Between different distance-eight components, off-diagonal coefficients are even and have absolute value at most 16, but they can be nonzero. Their contributions change each component's effective equations. A proof of an entire-support star, or of a single symmetric component, does not automatically exclude that component when coupled to another.

If a bounded antipodal solution survives, reconstruct \(f\) using the full inverse at all 512 vertices. Check that every value is in \(\{-1,0,1\}\) and that its adjacency sums equal the proposed sparse vector. Antipodal feasibility alone is insufficient. A verified nonzero \(f\) would be a count-recovery counterexample; additional connectedness and inducedness arguments would still be needed to obtain a snake result.

## Alternative proof-completion route

Complete the actual-cube Lean bridge for four or five missing counts.

The existing arithmetic is finite and explicit: 87 accepted four-position matrix implications, and 372 accepted five-position implications, recorded in the final Round 240 receipt. The missing assembly requires:

1. Extracting the finite exceptional support and splitting the selection difference by parity.
2. Connecting the cube inverse at antipodes to the correctly indexed matrix equations.
3. Proving that every relevant geometric configuration reaches an accepted matrix, or replacing that catalogue bridge with the written structural case argument where available.
4. Applying the accepted algebra and inverse to conclude that the whole selection difference vanishes.

Literal matrix acceptance does not discharge these steps. The fully assembled cube theorem remains three-count recovery until the additional bridge is checked.

## Interpretation of possible outcomes

- Exclusion of every six-position support would improve recovery to 506 observed counts and raise the minimum number of changed counts to at least seven.
- Exclusion of a restricted structural family narrows the remaining cases; it does not improve the unrestricted recovery threshold by itself.
- A valid six-, seven-, or eight-position recovery counterexample would settle that threshold from above and disprove the conjectured minimum nine.
- A bounded antipodal solution whose full inverse is nonternary would demonstrate the need for more inverse evaluations; it would leave recovery unresolved.
- Completion of the Lean bridge would strengthen verification of an existing theorem without changing its numerical threshold.

None of these outcomes alone changes the global snake-length interval or supplies a longer snake.

Use the frozen Round 239 completion record for older search states, and the completed Round 240 receipts for this round. Retain the existing single-heavy-worker and memory limits. Do not start global upper-bound work in this continuation.

