# Milestone 61: empty-square charge on the complete critical family

The empty-square calculation now covers the complete minimum-mean family of the nine-transition model, rather than one attaining cycle. The family has 49 states and 74 transitions in one strongly connected component. Longer-window validity restrictions alone leave its minimum unchanged. The new empty-square credits raise the restricted minimum from 3297/800 to **4961/1200**.

This is a result about the recorded critical family. It gives no new global upper bound: walks may leave that family, inherited numerical premises remain unresolved, and the complete arbitrary-snake graph assembly is unfinished. The contributor-checked interval remains **191 <= a(9) <= 235**.

## Complete family and longer contexts

The source is milestone 59's extended model with 1,026,432 states and 11,594,078 transitions. Its exact potential has nonnegative slack on every transition. Every minimum-mean cycle lies in the zero-slack graph. Removing all zero-slack edges outside cyclic components leaves exactly the recorded 49 states and 74 transitions.

The separate verifier checks every source inequality, both-direction reachability of this component, its complete edge set, and acyclicity of the remaining zero-slack graph. Thus the extraction covers the full source minimum family, rather than a sampled set of cycles.

Adjacent family transitions are extended by all nine possible coordinate choices, with unused-coordinate choices identified by canonical relabelling. Every longer window must be an induced path, and the overlapping count symbols must agree. This gives:

| Window length | States | Transitions | Rejected extensions |
|---|---:|---:|---:|
| Ten transitions | 74 | 121 | 0 |
| Eleven transitions | 118 | 218 | 28 |

The 28 rejected extensions have 27 distinct direction words. Each would select all twelve vertices of a cycle. Lean checks all 27 exclusions for arbitrary matching snake segments. The eleven-transition graph still has 112 cyclic states and 212 cyclic transitions, so these exclusions do not eliminate the entire critical family.

## Separating validity restrictions from empty-square gains

Each restricted graph is evaluated twice: first with the inherited nine-transition weights, then with the stronger forced-empty-square credits. The old and new credits are combined by taking their maximum on the same five centres.

| Context | Credits used | Exact normalized minimum |
|---|---|---:|
| Ten transitions | Inherited nine-transition credits | 3297/800 |
| Ten transitions | Extended geometric credits | 2477/600 |
| Eleven transitions | Inherited nine-transition credits | 3297/800 |
| Eleven transitions | Extended geometric credits | 4961/1200 |

All four minima have integer potentials checked on every edge and attaining twenty-step cycles. Lean checks each finite potential, proves the resulting inequality for every closed walk in that graph, and checks an attaining cycle and its weight sum.

In particular, every closed walk of length ell in the eleven-transition graph with the new weights satisfies

\[
10\sum_{i=0}^{\ell-1}w_i\ge4961\ell.
\]

The exact normalized increase over the source minimum is

\[
\frac{4961}{1200}-\frac{3297}{800}=\frac{31}{2400}.
\]

The comparison isolates the contribution of empty-square charging. The validity restrictions remove the previously studied cycle, but alternative cycles preserve the old minimum when the new share credits are omitted.

The ten-transition family minimum is also smaller than the 413/100 obtained from the single cycle in milestone 60. That earlier value was a cycle-specific calculation, as stated there. This confirms the need to inspect the full critical family when evaluating a proposed improvement.

## Geometric proof and remaining gap

There are 324 distinct longer-window shapes in these restricted graphs, of which 96 have positive geometric bounds. Each bound uses vertices forced absent by selected internal degrees, then counts empty squares with the available-neighbour count as a denominator upper bound. All 96 positive inequalities are checked in Lean for arbitrary matching snake segments. The other 228 table entries are zero lower bounds.

The independent computation enumerates all 4,608 square faces, reconstructs each forced-absence set and share term, exhaustively checks the longer-window transitions, and verifies all four potentials and cycles. The final Lean audit has 21 modules and 678 theorem-dependency checks, without admitted proofs. Source-family extraction and the complete finite lift enumeration are checked computations; their entire correspondence with arbitrary snakes is not claimed as a Lean theorem.

The new restricted minimum is still below the threshold needed for 234 with the present eleven-transition accounting. Even with zero potential-range loss, that target would require an integer-weight mean greater than 112440/225, whereas the restricted graph has mean 4961/10. Lean checks this arithmetic obstruction. A full enlarged model admitting this restricted cycle therefore cannot reach 234 using these same credits and boundary terms alone.

## Review of the approach and next test

The last rounds establish a consistent distinction. Selected-segment geometry supplies inexpensive, broadly applicable share bounds, while longer-window validity controls can remove a particular cycle without improving the full family's minimum. The share terms do improve the full family, but their current size is insufficient for the target bound.

A preliminary count-conditioned calculation was also made on the 58 critical edges containing a singleton count equal to one. Such a count leaves exactly one of 21 free opposite corners absent, allowing a direct enumeration of 21 alternatives. Using only that one count gives almost no additional share credit. Four edges have all branches contradictory in this preliminary calculation, but these are unproved candidate exclusions and they do not break all critical cycles. No result from this pilot is included in the checked graph bounds.

The next test is to combine the entire recorded count vector with forced-absence propagation, rather than using a single count or only lengthening the selected segment. This stays within the empty-square route and may expose absent corners that the selected segment alone does not determine. The pilot remains exploratory until its case split and deductions are checked in Lean.

## Files

- `scripts/critical.py`: extract the complete tight cyclic family.
- `scripts/lift_family.py`, `analyze_lifts.py`: construct and evaluate all ten- and eleven-transition family contexts.
- `scripts/prepare_lean.py`, `replay.py --resume`, `audit_lean.py`: local geometric, validity and finite-potential proofs.
- `scripts/verify.py`: separate exhaustive verification.
- `scripts/singleton_pilot.py`: explicitly unproved count-conditioned pilot.
- `data/verification.json`, `data/lean-audit.json`: verification receipts and scope.

This is research round 5 of 10 after manuscript revision 56. The paper and its open editor mirror remain unchanged and synchronized. The next scheduled full revision is milestone 66. The compilation limitation recorded in milestone 56 remains unresolved.
