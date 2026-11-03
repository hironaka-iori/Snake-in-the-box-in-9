# Independent review of Structural125

The saved Lean check passed in 25.890 seconds. This independent review verified the current source, object, log, checker, source/checker snapshots, all recorded dependency hashes, direct import resolution, and the matching successful run record. The audit covers 185 distinct verified files and four additional source/provenance pins. All 12 printed axiom reports agree with the receipt and contain only `propext`, `Classical.choice`, and `Quot.sound`. The source contains no definitions, placeholder proofs, or `native_decide`.

No mathematical indexing or scaling defect was found. The conclusions have different scopes and must remain separated.

The first three theorems concern six arbitrary natural variables. They derive totals of at least 17, at least 18, and at least 24 when the fourth variable is 2, under their displayed pair, exclusion, positivity, and outer-sum premises. The third result uses the explicit outer-sum premise of at least 19. These statements do not themselves prove that an actual snake window satisfies those premises. In particular, the source comment referring to the consecutive triple $(4,2,2)$ is not a substitute for an actual-window instantiation of `h422`.

The three abstract global arithmetic statements retain their total-count and square-budget hypotheses. `total_with_thirty_nine_deficits` supplies the finite-sum accounting for an arbitrary count sequence under endpoint and internal-count bounds. Its first 39 blocks cover internal positions 1 through 234. For $m\ge235$, there are exactly $m-235$ remaining internal positions. Natural subtraction measures each block's nonnegative deficit below 25, so

$$
T+D\ge m+748,
\qquad
D=\sum_{b=0}^{38}\left(25-\sum_{j=0}^{5}\alpha_{6b+j+1}\right).
$$

The actual-snake results instantiate these count facts with `coreAlpha`. The inspected `ActualUniform124` source, object, log, and saved snapshots match its inherited successful receipt. Its endpoint and internal-count facts require no unproved universal six-count floor.

The empty-square factor is correct. In the loaded `SquareIncidence` source, `AxisPair` selects an unordered pair of distinct coordinates, while `empty p ab v` tests absence of all four vertices of the corresponding square. `totalEmptyAnchored` sums this indicator over every pair and every vertex. Each ordinary square therefore occurs at its four corners. The source adjacent to the resolved object is byte-identical to the working source. An independent small enumeration also confirmed that the 18,432 pair/vertex anchors form 4,608 distinct ordinary faces, each with exactly four anchors. Emptiness depends only on the four-vertex set, so this establishes the interpretation $A=4s_0$, where $A=\mathrm{totalEmptyAnchored}$ and $s_0$ counts ordinary empty squares. This conversion was inspected mathematically; no new Lean conversion lemma was compiled or claimed.

The checked incidence identity is

$$
2A+4T+144(m+1)=36864+4W,
$$

and the checked wedge bound gives $W\le m-1$. For $m\ge1$, `retained_square_budget` consequently proves

$$
4T+140(m+1)+2A\le36856.
$$

Substituting $A=4s_0$ and dividing by 4 gives the manuscript inequality

$$
T+35(m+1)+2s_0\le9214.
$$

The ordinary empty-square term is thus $2s_0$; it must not be replaced by $2A$ in this divided inequality.

The remaining actual-snake consequences are precisely:

- For every actual snake with $m\ge235$, `actual_deficit_required` proves $58+A\le2D$, equivalently $D\ge29+2s_0$. This is an unconditional necessary condition at those lengths; it assumes no universal six-count floor.
- `actual_bound234_of_retained_deficit` concludes $m\le234$ if, whenever $m\ge235$, the explicit upper bound $2D\le56+A$ holds. In ordinary-square notation the required bound is $D\le28+2s_0$.
- Under a universal six-consecutive-internal-count floor of 25 and $m\ge234$, `actual_empty_at_most_fifty_two_of_floor25` proves $A\le52$, hence $s_0\le13$.
- With that universal floor and the additional hypothesis that $m\ge234$ implies $A\ge56$, `actual_bound233_of_floor25_and_empty` concludes $m\le233$. The empty-square hypothesis means at least 14 ordinary empty squares.

Neither the universal floor25, a universal floor23, the required deficit upper bound, nor the required empty-square lower bound is established by this module. The first three arithmetic lemmas do not discharge those hypotheses. No new unconditional snake-length upper bound follows from the reviewed results.

Evidence SHA256 pins:

- `data/proof-review.json`: `30d593f55cb50b009b2d459fc3542582dbb33240ff969893d8d7f993077fdf55`.
- `scripts/audit_receipts.py`: `5fd5267bfc545b95abddadb5b8bb8ab27a2512e7c893286b3d531f0efa315cfc`.
- `data/Structural125-audit.json`: `f8fd3fade96a9700a44494f24dcedf0711d95226ec4d7cafeb6e47c7416301fb`.
- `lean/Structural125.lean`: `ae32ad25578a5b34de9194d205b5ff5f13abe1ba7fc86ebaa3dc186e784bf38a`.
- `build-isolated/Structural125.olean`: `5161dfc8d93cabd52d8f99fb46212433d4a7291e50a242a0c8497b88e9e26b5a`.
- The loaded `SquareIncidence.lean` and its working copy: `3813aa1d9b451cf93c643ab8c954d599be1c646d5c633133bbef9dc9de261518`.

The JSON retains all log, checker, snapshot, import, and dependency hashes, including the resolved square-incidence object. Reproduction runs the audit script without an output argument for a summary, or with `--output` to create a new evidence file exclusively. This review ran no Lean compiler, solver, native contradiction replay, or full-graph computation; it did not rebuild the transitive library.
