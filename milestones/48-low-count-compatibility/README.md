# Low-count compatibility in short snake segments

Let $x_0,\ldots,x_m$ be an induced path in $Q_9$. Let $\alpha_i$ count the two-dimensional cube faces whose intersection with the path is exactly $\{x_i\}$. At an internal vertex, this is the number of unselected opposite corners among the 21 coordinate pairs disjoint from its two path directions.

For a segment starting at index $r$, the following restrictions have no hypotheses on the remaining counts or endpoint distances. The named coordinate labels in each row are distinct.

| Successive directions | Conclusion |
|---|---|
| $(a,b,c,d,a,b)$ | $\alpha_{r+1}+\alpha_{r+5}\geq5$ |
| $(a,b,c,d,a,e,b,a)$ | $\alpha_{r+4}+\alpha_{r+7}\geq6$ |
| $(a,b,c,d,e,c)$ | $\alpha_{r+1}\leq3\Longrightarrow\alpha_{r+5}\geq3$ |

The third statement is directional: the excluded pair of upper bounds is $(3,2)$. A saved local forest allows $(2,3)$ in a segment with the same first six directions. Interchanging the numerical bounds without also reversing the whole direction pattern is therefore unjustified by these local conditions.

## Proof structure and scope

Each argument starts with an arbitrary snake, selects the indicated segment, and normalizes its distinct coordinate labels by a cube automorphism. Its selected vertices satisfy the radius-four geometric constraints: prescribed segment membership, degree at most two, degree at least one where all neighbors are represented, at most two interior endpoints, absence of selected cycles, and the specified opposite-corner counts.

For the first two rows, assume respectively that the sum is at most four or five. A joint cardinality counter represents the sum exactly, preserving multiplicity when a vertex is counted at both centres. The resulting Boolean clauses have a replayed contradiction. For the third row, imposing both upper bounds three and two gives the contradiction directly. The arbitrary-coordinate statements then follow by undoing the normalization and using integer arithmetic.

The joint proofs include 289 and 16 additional selected-cycle exclusions, respectively. Every added set is checked to be a cycle, and its clause receives the same geometric interpretation as the ordinary clauses. The third proof needs no additional cycles beyond the ordinary encoding. The generated semantic proofs, replay, arbitrary-snake bridges and coordinate normalization are checked in Lean. See `data/verification.json` for the completed build and dependency audit; no claim rests solely on the search solver returning UNSAT.

| Result | Core clauses | Active variables | Derived clauses | Replay hints | Additional cycle cuts |
|---|---:|---:|---:|---:|---:|
| Sum at least 5 | 2,228 | 1,059 | 6,126 | 371,858 | 289 |
| Sum at least 6 | 1,467 | 1,008 | 2,124 | 179,865 | 16 |
| Exclude caps $(3,2)$ | 1,094 | 821 | 859 | 49,866 | 0 |

The twelve dependency audits permit only propositional extensionality, classical choice and quotient soundness. They do not use an admitted theorem or an unchecked native Boolean evaluation axiom. Earlier shared dependencies are reused from their checked builds; this round is not a fresh rebuild of the complete global-bound dependency tree.

## Controls and exact finite-model result

Independent geometry checks cover 38 saved positive local configurations and all 131 saved 191-edge snakes. The bank contains 3,018, 4 and 6,907 oriented occurrences of the three patterns, respectively. The minimum observed pair sums are 9, 17 and 11. These bank minima are observations, not stronger universal bounds.

The saved local configurations attain sums five and six for the first two restrictions. They can contain several path components and are not full-snake sharpness examples. The solver controls also show that some proposed symmetric pair-sum strengthening of the directional exclusion would fail in the local model.

Applying the three restrictions to every represented subsegment in both orientations excludes another 109,510 transitions from the milestone 47 graph. The graph has 1,586,304 states and 4,384,383 retained transitions. Its minimum normalized charge mean remains **42/11**. A new eleven-step cycle attains it. An integer potential satisfies

$$7056+\pi(v)\leq 11w(u,v)+\pi(u)$$

on every retained transition, with potential range 8,064. The independent verifier reconstructs the exclusions, checks every potential inequality, and checks all edges and weights of the attaining cycle. Count symbol six means an actual count of at least six; every newly excluded capped combination has both counted values strictly below six, so the exclusions do not confuse the capped symbol with an exact count.

This is an exact result for the specified finite graph. The complete graph-to-snake Lean bridge remains pending. The integrated global interval is still **191 <= a(9) <= 236**, and no 192-edge construction is established.

## Contributor refresh and next question

Contributor commit `ec37c2cd` reports experiments with longer direction-pattern exclusions. Several old critical shape cycles cannot be followed for a full period, but other cycles attain the same graph mean; some critical direction walks persist for more than 100 steps. That report expressly supplies no Lean build or SAT certificate. Its saved 235 build record remains incomplete. The two source notes and hashes are pinned under `sources/` and `data/contributor-snapshot.json`; their numerical claims have not been independently reproduced in this round.

All eleven windows of this round's replacement cycle are solver-excluded even when every count-six symbol is relaxed to 21. These new scout exclusions have no replay certificate yet. Thus the model still admits combinations which the stronger local geometry rejects.

The next focused task is a complete two-count survey on six-direction segments. There are nine direction shapes up to coordinate relabelling and reversal. Ten pairs of internal positions and the four cap pairs $(2,2),(2,3),(3,2),(3,3)$ give 360 candidate instances. A complete family may yield reusable restrictions across replacement cycles. `data/next-family.json` records the enumeration only; it does not claim the survey has been completed or that it will improve the global bound.

## Reproduction and manuscript cadence

`scripts/probe.py`, `pairs.py` and `shorten.py` generate the numerical discoveries. `certify.py` extracts the clause cores and generates replay sources; `wrappers.py` supplies the arbitrary-coordinate statements. `replay.py` builds in a fresh directory and supports source-checked resume. `archive.py --unpack` restores the lossless proof files.

`controls.py` checks the positive configurations and bank. `graph.py` updates the finite graph and finds a candidate cycle and potential. `verify.py` reconstructs the clauses and graph restrictions and verifies the proof provenance and exact finite-model certificate without rerunning the optimizer. `scout.py` records numerical tests of the replacement cycle.

This is research round **2 of 5** after manuscript revision 46. The paper and existing editor source remain unchanged; the new mathematical statements will be integrated at the next scheduled revision.
