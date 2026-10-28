# Milestone 62: empty-square share under a vertex case split

Eight stronger local empty-square bounds have been checked in Lean for arbitrary matching snake segments. They require only the direction word and the snake axioms; no singleton-count assumptions are needed. Applied to the existing eleven-transition critical family, they raise its exact normalized minimum from **4961/1200 to 2483/600**, a gain of **1/240**.

The global interval recorded by the project remains **191 <= a(9) <= 235**. This milestone does not improve that interval or establish the exact optimum. The graph result is restricted to the family extracted in milestone 61. The full graph-to-snake assembly and inherited numerical premises remain unresolved.

## Mathematical statement

Let S be the selected vertices of a snake, W a known selected segment, and C the five centres charged by the window. Write

\[
\sigma_{12}(S,x)=\sum_{q\sim x}\left\lfloor\frac{12e_S(q)}{d_S(q)}\right\rfloor,
\]

where e_S(q) is the number of empty square faces containing q and d_S(q) is the number of its selected neighbours. Every denominator here is positive because q is adjacent to the selected centre x.

For a candidate vertex z, consider both alternatives z outside S and z in S. In the first alternative, combine z with the vertices already forced absent by W, obtaining D0. In the second, use the selected set W together with z to force an absence set D1. Any candidate vertex whose selection creates degree at least three at a selected vertex is absent. The candidate itself may be the vertex witnessing this violation.

Set U_i=Q9 minus D_i and define

\[
L_i=\sum_{x\in C}\sigma_{12}(U_i,x).
\]

Then the **vertex-split share bound** is

\[
\sum_{x\in C}\sigma_{12}(S,x)\ge\min\{L_0,L_1\}.
\]

Proof: in each alternative S is contained in U_i. Consequently every square empty in U_i is empty in S, and d_S(q) is at most d_U_i(q). Both changes increase the share. The two alternatives exhaust the possible selection states of z. Taking their minimum gives the stated bound. The proof includes the positive-denominator condition and transport through arbitrary coordinate permutations and translations of the snake segment.

The mechanism retains credit that a single absence set loses: different alternatives can force different empty squares while guaranteeing a positive total in every alternative.

## Checked local improvements

The transition identifiers below refer to the 74-edge critical family saved in milestone 61. The old and new columns are lower bounds on the sum of the five integer shares.

| Transition | Previous bound | New bound | Split vertex in the canonical frame |
|---|---:|---:|---:|
| 7 | 6 | 10 | 8 |
| 8 | 6 | 14 | 8 |
| 21 | 0 | 7 | 4 |
| 22 | 0 | 4 | 4 |
| 27 | 0 | 6 | 46 |
| 36 | 5 | 8 | 10 |
| 39 | 5 | 11 | 43 |
| 50 | 0 | 8 | 43 |

For example, transition 8 has direction word (0,1,2,0,3,4,2,0,5), using zero-based coordinate labels. Splitting on vertex 8 gives two checked lower bounds whose minimum is 14. The previous geometric certificate gave 6. The complete direction words, branch absence sets and branch values are saved in `data/split-share.json` and instantiated in the eight local Lean theorems.

## Effect on the restricted critical family

The improved nine-transition bound is applied to the final nine transitions of each longer context. Its five charged centres then coincide with those of the longer window. Credits on those same centres are combined by their maximum.

| Context | Improved graph edges | Previous exact normalized minimum | New exact normalized minimum |
|---|---:|---:|---:|
| Nine transitions | 8 | 3297/800 | 9923/2400 |
| Ten transitions | 7 | 2477/600 | 397/96 |
| Eleven transitions | 11 | 4961/1200 | 2483/600 |

Each new minimum has an integer potential checked on every edge and an attaining cycle. Lean proves the potential inequality for every closed walk of each recorded graph. For the eleven-transition graph, every closed walk of length ell satisfies

\[
5\sum_{i=0}^{\ell-1}w_i\ge2483\ell.
\]

The integer-weight mean is 2483/5. With the present eleven-transition boundary accounting, even zero potential-range loss would require a mean greater than 112440/225 to obtain 234. The present mean falls short by 47/15. The actual potential also has nonzero range. No numerical improvement to the global bound follows.

## Exploratory work and evidence boundaries

The initial joint-count propagation pass covered all 74 critical transitions. Seven transitions have candidate contradictions; surviving cases obtained no additional share by that propagation alone. A separate verifier reconstructs 1,633 branch traces and 1,275 deduction steps. These count-conditioned results have no Lean replay and are excluded from the graph weights above.

A bounded further case split on eight selected test cases ended with unresolved branches. These results provide no impossibility claim.

A linear-programming relaxation then tested all 74 transitions. It suggested improvements on 27 transitions and reported no feasible branch on 29 transitions, including the seven propagation candidates. These are floating-point observations. The saved duals have not been converted into checked certificates. In particular, the candidate 492/49 on transition 7 is excluded from the certified table; the geometric theorem established here gives 10 on that transition.

The numerical calculation led to the vertex-split argument, whose proofs do not depend on trusting the solver, its candidate contradictions, or the count assumptions. The checked local bounds and the three finite graph certificates are independent of those exploratory numerical results.

## Verification and reproduction

- `scripts/propagate.py`, `branch_search.py`, `lp_share.py`: exploratory count and numerical searches.
- `scripts/split_share.py`: exhaustive one-vertex tests among neighbours of W not already selected or forced absent. It evaluates 63 distinct geometric shapes; the verification covers 926 trials across the 74 transition records.
- `scripts/analyze_graphs.py`: apply the eight improvements to the existing restricted nine-, ten- and eleven-transition families, find potentials and attaining cycles.
- `scripts/prepare_lean.py`, `replay.py --resume`, `audit_lean.py`: generate and check the local instances and finite graph certificates.
- `scripts/verify.py`: separate reconstruction using Hamming-distance adjacency and all 4,608 global square faces; checks branch deductions, local share arithmetic, graph weights, potentials and cycles.

The successful Lean audit contains **12 modules and 88 theorem-dependency checks**, including all eight arbitrary-snake instances and three all-closed-walk bounds. Dependencies are limited to the standard axioms propext, Classical.choice and Quot.sound; no admitted proofs occur. `data/verification.json` and `data/lean-audit.json` record the exact scope and receipts. Finite graph coverage and the final-nine-transition matching are separately checked computations, with the full arbitrary-snake graph assembly still pending.

## Next step and manuscript schedule

The next test is to apply the same vertex-split share bound directly to the eleven-transition windows on the new attaining cycles, then evaluate the complete restricted family again. This keeps the focus on empty-square charging and tests whether longer selected context strengthens both alternatives. Only if single splits cease to improve the relevant cycles should deeper case trees be considered.

This is research round **6 of 10** after manuscript revision 56. The next full paper rewrite remains scheduled for milestone 66. The repository paper and the existing editor mirror are unchanged and have the same SHA-256 digest. The manuscript compiler limitation recorded in milestone 56 remains unresolved.
