# Milestone 63: vertex splits on eleven-transition windows

Direct vertex splits on longer windows give **38 stronger local empty-square bounds**, each checked in Lean for arbitrary matching snake segments. The exact normalized minimum of the existing eleven-transition critical-family graph rises from **2483/600 to 4973/1200**, an increase of **7/1200**.

The project interval remains **191 <= a(9) <= 235**. The new result concerns the restricted critical family. It supplies neither a new global upper bound nor the exact optimum.

## Local argument and exhaustive search scope

The vertex-split share theorem from milestone 62 applies at arbitrary window length. For each eleven-transition segment, its final five internal vertices are the charged centres. A candidate vertex is either absent or selected. In each alternative, selected degree at most two forces an absence set. Counting empty squares against that absence set gives two share bounds; their minimum is valid for the original segment.

All 218 transitions of the restricted graph were considered, representing 214 distinct direction shapes. Initially the split vertex was restricted to neighbours of the segment. A second pass allowed every vertex of Q9. Known selected or already forced-absent vertices have no useful case distinction and were omitted. For any remaining vertex, the minimum of the two branch values cannot exceed the absent-branch value. This permits a candidate to be discarded when that value is no better than the best completed split.

The independent verifier reconstructs **94,432 split candidates on the 214 distinct shapes**, including 89,436 candidates discarded by this exact comparison. It checks all 4,608 square faces using separately constructed Hamming-distance adjacency. The all-vertex search gives the same best values as the initial neighbourhood search.

This coverage is exhaustive for the specified one-vertex split and degree-forcing rule. It is not an exhaustive search over every possible local deduction, deeper case tree, or snake.

The 38 improvements have no additional singleton-count assumptions. For each, Lean checks both forced-absence sets, both finite share calculations, positive denominators, and transport to every matching snake segment under coordinate permutation and translation. The direction words, split vertices, old bounds and new bounds are recorded in `data/splits.json`; the instances are in `lean/Edge*.lean`.

## Restricted graph result

The graph retains its 118 states and 218 transitions. Each new local share bound is combined with the inherited bound by taking their maximum, since the same five centres are charged. The remaining part of the edge weight is unchanged.

The resulting integer-weight mean is 4973/10. An integer potential valid on every edge and an attaining twenty-edge cycle establish the exact finite minimum. Lean checks these certificates and proves that every closed walk of length ell satisfies

\[
10\sum_{i=0}^{\ell-1}w_i\ge4973\ell.
\]

In normalized units the improvement is

\[
\frac{4973}{1200}-\frac{2483}{600}=\frac7{1200}.
\]

The potential range is 6013. Even with zero range loss, the current eleven-transition accounting would require an integer-weight mean greater than 112440/225 to obtain an upper bound of 234. The exact gap is

\[
\frac{112440}{225}-\frac{4973}{10}=\frac{73}{30}.
\]

Both this comparison and the gap are checked in Lean. The attaining cycle also shows that changing only the potential cannot reach the target with these same edge weights. A complete snake model containing this cycle would inherit the same obstruction unless its constraints or weights were strengthened.

## Verification

The successful audit contains **39 Lean modules and 348 theorem-dependency checks**. It covers 38 arbitrary-snake local inequalities, the all-closed-walk bound, an attaining cycle, and the threshold arithmetic. No admitted proofs occur; dependencies are limited to propext, Classical.choice and Quot.sound.

The separate verifier checks the exhaustive single-split coverage, branch arithmetic, correspondence to the preceding graph, every potential inequality and the attaining cycle. These are checked computations. The full graph-to-snake assembly and inherited numerical premises remain unresolved, as in the preceding milestones.

Relevant receipts are `data/lean-audit.json`, `data/verification.json`, and the saved module logs. The scripts are:

- `search.py`: all-vertex single-split calculation with exact branch-value pruning.
- `analyze.py`: restricted graph weights, potential and attaining cycle.
- `prepare_lean.py`, `replay.py`, `audit_lean.py`: local and finite graph proof generation, replay and dependency audit.
- `verify.py`: separate geometric and integer reconstruction.

## Preliminary comparison of the next methods

Two further computations were made on the saved twenty-edge attaining cycle. Neither is included in the certified weights above.

1. Retain the chosen first split and optimize a second split in each branch. This gives a candidate total improvement of 8 integer-weight units over the cycle.
2. Enumerate all possible additional selected neighbours at the two ends of each window. Each end already has one selected neighbour inside the window, so it can have at most one additional selected neighbour. For each joint choice, declare the unchosen neighbours absent and derive its empty-square credit. This gives a candidate total improvement of 19 units over the same cycle.

The second computation currently has no Lean case-coverage proof and has not been evaluated over the complete family. Its use of the window ends concerns local degree and empty-square credit only; it introduces no charge based on the number or position of snake endpoints.

The current cycle would require more than 146/3 additional weight units to cross the zero-range threshold. Thus even the 19-unit pilot gain would be insufficient by itself. The neighbour-choice enumeration is the more useful next test because it has the stronger measured gain and a finite case-coverage statement that can be proved. Its evaluation must include the entire restricted family, since a different cycle can become minimal.

The raw pilots are `data/two-split-pilot.json` and `data/neighbour-pilot.json`. They remain exploratory; no global bound or exact stronger family mean is claimed from them.

## Repository and manuscript

This is research round **7 of 10** after manuscript revision 56. The paper and existing editor mirror remain unchanged and synchronized. The next scheduled full rewrite is milestone 66. The compiler limitation recorded in milestone 56 remains unresolved.

The next research task is to prove the neighbour-choice case coverage, certify its empty-square bounds, and evaluate the complete restricted family. This continues the selected empty-square route.
