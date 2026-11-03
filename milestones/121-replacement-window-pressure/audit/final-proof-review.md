# Final proof receipt review

The independent receipt review passes for all 40 completed modules: the 34 concrete certificate modules, the actual-snake pair theorem, reference coverage, three boundary witnesses and conditional endpoint arithmetic. All 47 printed axiom reports agree with their logs and receipts. The audit verified 357 distinct recorded source, compiled-object, log, snapshot and dependency files, including resolution of every direct import to the intended object.

No compiler, solver, graph calculation or proof replay was launched. This is an integrity and statement-scope audit of saved successful checks. The complete evidence is `data/final-receipt-review.json`, SHA256 `7011b59330d95202bb52fe245b4c1eae789daa947148facc0a8bb4d96b7eecab`; the reproducible script is `scripts/audit_final_receipts.py`, SHA256 `5236dcd67bc37319688bb67fadb390a7a4aff6531a654486fc29fd27ce8d1e77`.

## Checked pair theorem

For an actual snake and a fitting six-transition window with canonical word $012032$, `ActualPair121` proves

$$
\alpha_{r+2}\ge2,\qquad \alpha_{r+4}\ge2,\qquad
\alpha_{r+2}+\alpha_{r+4}\ge8.
$$

The concrete minima and sum statements require only the snake, the fitting-window inequality and the canonical direction match. They have no remaining local-contradiction or reference-catalogue premise. Their three concrete local refutations respectively exclude caps $(1,21)$, $(2,5)$ and $(3,4)$ on the second and fourth counts, with the other counts unrestricted within $[0,21]$.

The checked reversal argument applies the forward exclusion to the reversed actual snake, uses the existing direction and count reversal lemmas, and verifies that canonical reversal fixes $012032$. It does not assert an unproved general reversal theorem for the raw local `Refuted` predicate. The final arithmetic uses both orientations to cover every pair whose sum is at most seven.

The reusable encoded `actual_forward` and `actual_reverse` statements still have an explicit `href` premise and the conditions that each cap is below six or equals 21. Their concrete uses must supply one of the checked refutations. This distinction is preserved: the general guard interface remains conditional on its supplied refutation, while the concrete actual-snake minima and sum have that premise discharged.

The final source is unchanged from the prepared source, SHA256 `17732a533cc39f73a1d140a69e5b666260a0fdc3ae5731611ff15b5f45090280`. Its compiled object is `5ca5bed6c8d796d2d3572da71b08d3bf27ee186915b2e7c048483de213787e0f`, and its receipt is `03a00163d46b754fe8fbc28f2dfdcfbfd9206d4b88c07d44b5398483b95c61ae`.

## Catalogue and attainment

The five newly checked entries are the direct-orientation indices 196 through 200:

$$
(2,2,6,5,2),\ (2,2,6,5,3),\ (2,3,6,3,2),\
(2,3,6,3,3),\ (2,3,6,3,4),
$$

all on direction word $012032$. Symbol six retains $[6,21]$. The first two use the $(2,5)$ refutation and the other three use $(3,4)$. The source appends the fifteen previously checked keys using their existing theorem. The independent literal check verifies all twenty distinct members, the five exact indices and the filtered length 1358. The checked union equivalence leaves refutation of those 1358 entries as the unresolved catalogue obligation.

All three boundary modules now have successful Lean receipts. Their literal vertex arrays, path lengths, designated direction words and exact pair positions were checked against the independent path audit. The pair counts were independently recomputed again during this receipt review.

| Module | Snake length in edges | Window start | Count positions | Exact pair |
|---|---:|---:|---|---|
| `Boundary26` | 142 | 120 | $(122,124)$ | $(2,6)$ |
| `Boundary35` | 138 | 114 | $(116,118)$ | $(3,5)$ |
| `Boundary44` | 144 | 136 | $(138,140)$ | $(4,4)$ |

Each checked module includes distinctness, inducedness, the actual direction sequence, its canonical form $012032$, the exact two counts and existential attainment of sum eight. These witnesses establish that the pair-sum lower bound cannot be raised universally. The first witness attains the separate minimum two; reversal supplies its counterpart for the other counted position. The witnesses do not improve a longest-snake construction.

## Endpoint statement remains a hypothesis

`EndpointArithmetic121.conditional_charge_bound` is now checked. It is an integer arithmetic implication from the explicit premises

$$
d\ge0,\quad C\ge0,\quad t\le14,\quad
W+4200m\le1098960,\quad
p(m-8)-R\le d(W+Ct)
$$

to

$$
(4200d+p)m\le1098960d+14Cd+8p+R.
$$

The module neither proves that $t$ counts equality windows nor establishes $t\le14$ for a snake. It also supplies no modified graph potential. Its receipt is `12f39ca916b2a31782fe223c357b2c8e0ec7fcf6da68360d357515fb16b52ea3`.

The three endpoint probes retain status `UNSAT_UNCERTIFIED`, radius nine and zero cycle cuts. Their saved encoding/provenance audit explicitly lacks a refutation replay and a Lean endpoint theorem. The review verifies these records and their hashes, and checks that the two counted vertices have the listed fourteen common distance-two neighbours. Both endpoints of each saved boundary witness lie in that intersection, which remains a finite observation.

The mathematical note correctly labels the general endpoint-location statement as a hypothesis. Under that hypothesis, its parity consequence and the maximum-fourteen argument are mathematically consistent: distinct endpoints have distance-two sphere intersection sizes fourteen at distance two, six at distance four and zero otherwise, and different window starts have different first counted vertices. These conditional arguments have not been integrated in Lean. The warning about a clipped $(2,6)$ pair is necessary: symbol six may represent an actual count above six, so the encoded pair alone does not establish equality of the actual sum to eight.

The inspected mathematical note has SHA256 `be84f241b721b9666b7e0493510aef8b1bd86cdb541c00590ff6fea9dd20816d`. Its statement that the conditional arithmetic passes Lean agrees with the successful receipt. No endpoint hypothesis, frequency theorem or improved global bound is promoted by this review.

## Receipts and limitations

| Module | Seconds | Printed axiom reports |
|---|---:|---:|
| `ActualPair121` | 40.844 | 18 |
| `ReferenceCoverage121` | 16.563 | 4 |
| `Boundary26` | 39.297 | 8 |
| `Boundary35` | 41.079 | 8 |
| `Boundary44` | 75.687 | 8 |
| `EndpointArithmetic121` | 11.344 | 1 |

The 34 preceding certificate modules also have successful source/object/log receipts. Across all printed statements, eighteen reports use `propext`, `Classical.choice` and `Quot.sound`; sixteen use `propext` and `Quot.sound`; twelve use only `propext`; and one uses no axioms. No reviewed source contains `sorry`, `admit` or `native_decide`.

The evidence preserves every run-record, receipt, source, object, log, snapshot and recorded dependency hash, plus import paths and axiom lists. The historical candidate/source-only reports remain unchanged as records of their earlier stages; their specific pair, reference and boundary compilation gaps are discharged by the final receipts reviewed here. The earlier unused `ActualOuter121` export is not among the forty checked modules. Full-graph experiments and the maintained global interval were outside this receipt audit and are not established by these forty modules.
