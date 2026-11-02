# Independent final review of milestone 111

This review found no mathematical defect in the checked three-count restriction or its transfer to actual snakes. It independently verified the saved proof records and replayed both contradiction certificates without invoking Lean or a SAT solver. The sorted sum certificate is a verified native contradiction; its concrete count semantics and actual-snake theorem remain unfinished. No reviewed graph experiment improves the integer comparison.

The review wrote only this report. It did not alter proof sources, receipts, graph data, or the running milestone 104 work. Checks described below were executed from inline Python commands; the existing evidence files were read without being overwritten.

## Checked restriction and proof records

`lean/MiddleCount111.lean` proves the exclusion for the six-transition canonical word $(0,1,2,3,4,0)$ with five count intervals

$$
([0,21],[0,3],[0,2],[0,5],[0,21]).
$$

Consequently, for a fitting actual snake window starting at $r$,

$$
\alpha_{r+2}\ge 4\quad\text{or}\quad
\alpha_{r+3}\ge 3\quad\text{or}\quad
\alpha_{r+4}\ge 6.
$$

The first and fifth internal counts retain their universal upper bound 21. The actual-window theorem requires $r+6\le m$. The two graph-facing theorems require $r+9\le m$ and $s\le1$, and exclude the appropriate five-count interval test at offset $s$, in each orientation. Their direction slice starts at offset $s+2$. These statements use the existing canonical-window and encoded-interval exclusion lemmas, so the count and transition indexing agree.

The canonical reversal of this direction word is again the same word. Reversing the count interval therefore exchanges the two unequal middle caps, producing $(5,2,3)$ in place of $(3,2,5)$. The graph filter implements precisely that union. Its tested caps are below 6, so the interpretation of count symbol 6 as $[6,21]$ causes no ambiguity.

All 58 successful module receipts were checked against their current sources, immutable source snapshots, compiled objects, logs, and recorded receipt hashes. The 13 printed axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the finite metadata check uses only `propext`. No reviewed proof source contains `sorry`, `admit`, or `native_decide`. These are checks of the recorded build and bytes, without a fresh rebuild of historical dependencies.

The main contradiction was independently reconstructed and replayed. The generated radius-four geometry and 13 saved cycle clauses reproduce all 55,229 full CNF clauses. Each cycle clause was checked against a selected vertex set satisfying the generator's cycle criterion. The decoded Lean input is exactly the 2,040 selected core clauses. A separate Boolean-assignment implementation of ordered unit propagation verifies all 11,711 derived clauses and 611,907 hints, ending at empty clause 68,838. It does not rely on the verifier in `scripts/audit.py` for that replay. The latter script's source was also inspected, including its clause-number mapping, port identity, dependency checks, and final scope statement.

`CounterSound111` supplies generic counter soundness under explicit literal-validity and count-bound hypotheses. Its six checked theorems do not discharge those hypotheses for the proposed sum counter. There is no implicit sum theorem in this helper.

## Sorted sum certificate

The candidate is

$$
\alpha_{r+3}\le2\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge22.
$$

For the canonical vertex window $(0,1,3,7,15,31,30)$, the review rebuilt the four corner-literal lists at internal centres 1, 2, 4, and 5 directly from the adjacent path directions. Each list has 21 negative corner literals. Their concatenation has 84 occurrences, comprising 77 distinct literals: 70 occur once and seven occur twice. Sorting preserves all 84 occurrences. Deduplication would change the represented sum.

Using the saved generator's sequential-counter implementation with cap 21 reproduces the complete sorted CNF byte for byte: 3,085 variables and 58,438 clauses. The 4,774 core identifiers are distinct, and the saved core CNF equals exactly those clauses of the full file. Independent ordered unit propagation then validates 71,388 deductions and 6,105,267 hints, ending at empty clause 166,859.

This establishes the native contradiction for the precisely reconstructed encoding. Remaining obligations include the concrete counter-metadata check, the equality between its literal count with multiplicity and the four actual counts, the required counter bounds and base-literal validity, the Lean contradiction, and the transfer to actual snake windows. The generic counter theorem alone supplies none of those concrete identities.

The older unsorted attempts retain their original status. The standalone LRAT generation timed out at 60 seconds, and the two DRAT verification attempts timed out at 60 and 180 seconds. A separate native solver reported unsatisfiability for the unsorted instance, but its saved partial or unchecked proof files do not constitute a successful verification. The sorted certificate is a separate successful reconstruction and replay.

## Local witnesses

The four saved positive local witnesses were independently checked for window inclusion, radius-four membership, induced degrees, interior endpoint budget, acyclicity, and exact counts. A component edge-count calculation verifies acyclicity independently of the saved audit's peeling implementation.

| Exact count tuple | Selected vertices | Components | Interior endpoints |
|---|---:|---:|---:|
| $(9,3,8,2,3)$ | 116 | 7 | 2 |
| $(11,3,2,6,12)$ | 117 | 26 | 2 |
| $(11,4,2,4,9)$ | 119 | 23 | 2 |
| $(12,4,2,5,9)$ | 122 | 24 | 2 |

These sets satisfy the current relaxed local model. They prevent the corresponding stronger exclusions within that model. Their multiple components and relaxed boundary conditions do not provide complete long snakes or disprove stronger statements using global connectivity. The first tuple has outer sum 17, as claimed.

## Graph experiments and comparison scope

Both experiments start from milestone 110's checked-count graph, with the same 2,957 previously removed keys. They are separate experiments.

| Additional assumption | Additional deletions | Remaining keys | Completed mean/range | Conditional mean/range |
|---|---:|---:|---:|---:|
| Checked middle-count exclusion | 1,462 | 4,942,589 | $483/551$ | $496/602$ |
| Proposed outer-sum inequality and charge | 1,622 | 4,942,429 | $483/551$ | $496/602$ |

The two newly deleted sets are disjoint. Their intersection consists exactly of the 2,957 baseline deletions. Thus the second experiment must not be described as removing only 160 more keys than the first or as a cumulative strengthening of its graph.

A subsequently saved combined experiment removes the union of these sets: 6,041 keys in total, leaving 4,940,967. The review inspected `scripts/combine_experiments.py`, verified its recorded input hashes and exact deletion union, and confirmed that both displayed cycles survive. The script reconstructs the same weights and proposed suffix bonus, verifies the saved sum-profile potentials on the intersection graph, and checks attaining cycles. The previous potential inequalities also remain valid on this smaller edge set. Thus the combined native result is consistent with the unchanged comparisons. Its sum and excess-budget assumptions remain explicit.

The sum experiment tests both placements for deletion, but awards the candidate excess credit only at the suffix placement. Its coefficient 30 corresponds to distributing coefficient 120 over four fixed count positions. The arithmetic is compatible with an eventual overlap argument; the actual sum inequality and the clipped-count boundary argument remain necessary proof obligations. It adds this proposed excess credit to the existing weight rather than replacing existing share credit.

The review checked the deletion-list sizes, baseline relations, all four saved cycle chains and their surviving full keys, exact cycle weights and means, potential-file hashes and lengths, minimum zero and recorded ranges, and potential inequalities on the displayed cycle edges. It also verified the exact comparisons

$$
\frac{1098960+8\cdot483+551}{4200+483}
=\frac{157625}{669},\qquad
\frac{1098960+8\cdot496+602}{4200+496}
=\frac{551765}{2348},
$$

whose integer floors are 235 and 234. Exhaustive edge-wise potential verification and potential generation were not rerun in this independent review. Their recorded results remain native finite computations; they are not a complete Lean certificate for either revised graph. The recorded range is the range of the supplied potential, without a new minimal-range claim.

Both surviving cycle families now have only count symbols below 6. The completed cycle has count period $(3,4,5,4)$ up to rotation. Its suffix middle count is 3 in the relevant shape. The conditional surviving cycle is also unsaturated. An additional credit depending solely on count hidden above 6 vanishes on these particular recorded cycles.

A final family experiment was saved during this review. It combines the checked middle restriction with three assumed outer-sum lower bounds: 22 when the middle count is at most 2; 19 when it is at most 3; and 17 without a middle restriction. The implementation chooses the strongest applicable bound once. It deletes violated exact-symbol windows at either placement and applies the candidate coefficient-30 excess bonus only at the suffix. It does not add the three alternative deficits together. If the middle symbol is 6, the unconditional threshold 17 is used, consistently with symbol 6 representing $[6,21]$.

This experiment removes 7,999 additional keys beyond the checked middle graph, leaving 4,934,590. Independent inspection verified the input pins, deletion counts, the saved cycles against the original full-key graph arrays, their reconstructed baseline weights and bonuses, potential-file hashes and ranges, and exact comparison arithmetic. The completed profile has a 14-edge attaining cycle with mean $3384/7$, recorded range $3860/7$, and comparison $1930913/8196$, whose integer floor remains 235. The conditional profile has a three-edge cycle with mean 496 and range 602, retaining integer comparison 234. The completed mean improves from 483, but this small conditional improvement does not change its integer comparison. As above, the independent review did not rerun every edge inequality. All three sum theorems and their common excess-budget integration remain unproved.

## Mathematical note and remaining limitations

The reviewed `mathematical-note.md` correctly separates the checked three-count theorem, the native sum contradiction, local witnesses, and incomplete graph integration. Its observed probe times agree with saved records: 13.468 seconds for the unsorted probe and 1.985 seconds for the sorted probe. These observations do not establish a controlled or general performance improvement. The original middle-at-most-3 probes with outer caps 18 and 19 retain `UNKNOWN`. A subsequent sorted-input probe for cap 18 reports `UNSAT_UNCERTIFIED` in 1.531 seconds with zero added cycle clauses. It has no checked contradiction certificate in this review. The unrestricted-middle cap-16 probe likewise retains `UNSAT_UNCERTIFIED`.

The numerical optimum of the optional continuous relaxation was not independently re-solved in this bounded review. Its statement is explicitly computational. The historical upper-bound rebuild, remaining 1,366 reference entries, exact optimum, and conjectured 196 are outside what this milestone proves. No improved snake bound follows from this round.

## SHA-256 evidence pins

Paths below are relative to this milestone unless otherwise indicated. Individual module hashes remain in the independently checked 58 receipts, indexed by `data/proof-summary.json`.

| File | SHA-256 |
|---|---|
| `lean/MiddleCount111.lean` | `e2a441db91bff8fa5c3c850ff389df1c34648c3e331a5f54d45fdbe72305044d` |
| `data/MiddleCount111-audit.json` | `92cb3200db37099d9585311c78d6043a43b08325b47878b4546dc0be58930945` |
| `data/proof-summary.json` | `7f2ca5b73caf94a79b0f7cd5e53f500f06895b38e9606b55ead208b35ebd3b6d` |
| `scripts/audit.py` | `160c66c2887bcc2a94b0390d0602f3f164a50047909ce9ea0ea7c25bae89e07a` |
| `work/middle-refined/middle325r.cnf` | `859b63bcd099c7a434a09fe492a9f13acbaa863ccb6d3fb558f8009f55d348f5` |
| `work/middle-refined/middle325r.lrat` | `fc3821af3e4ed2e20988a395e92385ee7366576a5eab22b39f5f99c5e9edeba3` |
| `data/sum21-sorted-core.json` | `4bfe6769f4d02c7df5560126605c7cc25c1c49f01567ff3f7b90d0e16f4fea23` |
| `work/sum21-sorted/full.cnf` | `a8d375f9ba66574a1da5c2fdc44bfcf6038da97be32bd0d8c03fde31af2c0e9c` |
| `work/sum21-sorted/core.cnf` | `60cc2e5c35a9d4932c0d65a404c9c16e8227e8a0ca79785319a36807277e87f0` |
| `work/sum21-sorted/full.trim.lrat` | `b8bab175fc7ce16412d76c30be625d8d6130f56eb5f5748faeeb0f6c7401a669` |
| `data/witness-audit.json` | `9056123bf929d60bcca1f2b6c0fd25e63d18451d7980c147d871628d689e78b8` |
| `data/middle325-profiles/results.json` | `299657bc139785919b8a0114e6ef60bd42a9572f641c11a10990aa094043421a` |
| `data/sum22-profiles/results.json` | `439c4460c08522cc40e144572f046e6b64238fe7fba22589d8b7be480af08bf5` |
| `data/combined-experiment.json` | `f99d01d7655871ce31e133e380f71cb378eb80728a83dddb3a25681590abbb65` |
| `data/probes/centre3-sum18-sorted.json` | `41fd75bf1c242c4bc4ae4577547f03274816444ef11f5cb642214daa5fb5b3ea` |
| `data/family-profiles/results.json` | `1574a0780b6513b3edb63118bbb609464ae6741023a0792bfe57e38f7cc9ba77` |
| `mathematical-note.md` | `8c9c593676a8b1d241fac0c2c587ee0d456a80a99da71f953bac798ef1c75cf4` |
