# Final bounded review of milestone 117

## Conclusion and scope

The conditional geometric theorem, comparison arithmetic and native certificate records are consistent with the saved evidence. The candidate remains

$$
012034,\quad\alpha_{r+3}\le5
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge16.
$$

The native contradiction does **not** yet establish a completed Lean theorem for this inequality. The checked geometric result retains an explicit local-contradiction premise. Concrete joint-counter semantics, the full Lean contradiction and their composition remain outstanding.

This review inspected source and checker logic, verified the successful source/object/log/snapshot hashes, checked certificate-record links and exact input-clause mapping, and hashed both selected trimmed proofs. It did not repeat either large propagation replay, rebuild the dependency closure, reconstruct every generated clause, run Lean or a solver, or rescan the graph.

## Checked geometric and arithmetic statements

`SumGeometry117.lean` contains exactly three theorem declarations and no new definitions, structures, inductive types or axioms. Its source contains no `sorry`, `admit` or `native_decide`.

Compared with `SumGeometry112`, the transfer retains the same coordinate-normalization and count-identification argument. The word is changed to $012034$, its canonical vertices are $(0,1,3,7,6,14,30)$, the middle cap is five, and the negative outer-sum threshold is fifteen. The selected centre records are

$$
(1,0,1),\quad(3,1,2),\quad(6,0,3),\quad(14,3,4).
$$

These correspond exactly to internal positions one, two, four and five. The theorem assumes $r+6\le m$ and the canonical word equality. The ordinary internal upper bound 21 supplies the other four count bounds. `hlocal` explicitly quantifies selected-vertex and endpoint functions satisfying the local axioms and asserts that their selected absent-corner sum cannot be at most 15. Applying the existing frame and count lemmas then gives the displayed actual-snake implication. The proof does not silently supply `hlocal`.

The arithmetic theorems state:

$$
6p\le2915d\quad\Longrightarrow\quad
(4200d+p)235\le1098960d+8p+R
$$

for natural $p,d,R$, and

$$
\frac{1098960\cdot6+8\cdot2915+3460}{4200\cdot6+2915}
=\frac{1324108}{5623}.
$$

These statements are correct and make no claim that the new graph has a completed actual-snake interpretation. Interpreting $p/d$ as a slope additionally requires $d>0$.

The successful receipt records exit code zero, no timeout, and 13.906 seconds. Its three printed audits are:

| Theorem | Printed axioms |
|---|---|
| `comparison_barrier` | `propext`, `Quot.sound` |
| `comparison_value` | `propext`, `Classical.choice`, `Quot.sound` |
| `actual_outer_sum` | `propext`, `Classical.choice`, `Quot.sound` |

Current source and source snapshot agree. The current object and saved log match their receipt hashes. The initial attempt is preserved as `PREPARED`, without a launcher PID or exit code; its checker snapshot places the failing resource assertion before any compiler launch. It is not a failed Lean proof attempt.

There is one non-mathematical receipt caveat. The successful receipt's `other_lean_processes` still lists the two processes seen during the last waiting iteration. The checker refreshes its local process list and asserts the one-other-process gate immediately before launch, but does not copy that final successful observation back into the saved field. Thus the field is stale waiting-state metadata and should not be cited as the launch-time inventory. This does not affect the theorem source, object or axiom evidence. No checked artifact was edited to repair that metadata.

## Native certificate and refinement

The certifier constructs the canonical radius-four model with bounds

$$
[0,21],\ [0,21],\ [0,5],\ [0,21],\ [0,21]
$$

and appends a sorted threshold counter for the four outer absent-corner lists. It sorts literal occurrences without deduplicating them. I independently enumerated the four corner lists from the displayed vertices: they contain **84 occurrences and 78 distinct corners**. The saved probe has no added cycle cuts. The full generated formula has 57,559 clauses and 2,644 declared variables.

| Stage | Input clauses | Used input clauses | Deductions | Propagation hints |
|---|---:|---:|---:|---:|
| Original retained native certificate | 5,662 | 5,662 retained | 159,380 | 13,252,922 |
| Selected `core0` refinement | 5,662 | 5,114 | 142,180 | 8,712,029 |

The refinement uses the same extracted input formula. I compared its 5,662 clauses, including literal order and repetitions, with the designated clauses of the full formula. The original core IDs equal the refinement's input IDs; the 5,114 used original IDs form a subset. Both trimmed proof hashes and the exact record-to-record certificate hashes match.

The refined replay maps input IDs through that explicit list and maps derived IDs above the full input range. It requires increasing derived IDs, existing antecedent clauses and a contradiction obtained by unit propagation under the negation of every proposed clause. Finally it requires the empty clause and the exact recorded deduction and hint counts. The same propagation principle appears in the initial certifier. Inspection found no step that treats solver UNSAT output alone as a replayed contradiction.

`refine-core0.json` intentionally retains `UNSAT_TRIMMED_NOT_REPLAYED`; the later separate `replay-core0.json` records `PASS_REFINED_RUP_IN_ORIGINAL_FORMULA` and pins that immutable refinement record. These statuses are consistent. The replay records 1,709 distinct active variables. This is an active-variable count, not an already certified renumbered Lean export; the original formula still declares 2,644 variables.

## Graph and documentation consistency

The existing independent graph review remains applicable: the completed profile has mean $2915/6$, range $1730/3$ and integer comparison 235; the conditional profile has mean 496, range 602 and integer comparison 234. The saved replacement cycles have zero deficits throughout the fixed eleven-rule family. No repeat graph audit was performed here.

The mathematical note was present and reviewed at the hash listed below. It preserves the distinctions between native replay, a conditional Lean transfer and a completed actual-snake theorem. Its mean increase $41/78$, range decrease $478/39$, comparison values and zero-range obstruction are arithmetically correct. Its proposed next $012301$ test is explicitly untested.

The note's positive control agrees with `data/witness-audit.json`: counts $(5,3,5,3,6)$, outer sum 17, and component sizes $39,27,19,14,9$. That audit reports 108 selected vertices and two represented interior endpoints. This review checked the record and its stated scope without repeating its adjacency audit. The local forest is not a complete snake witness. The stronger outer-sum and total-count probes remain UNKNOWN as stated.

`README.md` was absent at the final documentation check for this review. Its eventual contents and any later revision of the mathematical note are outside the pinned review. No substantive mathematical defect was identified in the inspected note.

## Exact pins

| Artifact | SHA256 |
|---|---|
| `lean/SumGeometry117.lean` and its successful source snapshot | `071bc9edc979abdf0c35aa96ef9ddbdbc3bb2eeec00b85c9589cdf0ca1df4ce5` |
| `build-geometry/SumGeometry117.olean` | `81585382fc5ea26b2f2ed5ec18df74b014d586d42bf4fde687036102cfd3065c` |
| Successful Lean log | `70eb06e074d7504860269e258ac1da4f3084477d03acc6e4762016edcb8ea4c4` |
| Successful checker snapshot | `770e0e46ad9c5e690adb4bf1bf8ae0bdb91ff3a5fa89a3e6399e79aada5f27fb` |
| `data/SumGeometry117-audit.json` | `5f8e5918f5371e7aeb515ea6dc5c0ae241ef2fb1c7ee3189ecce1b169b72e88f` |
| `scripts/certify_sum.py` | `fb9ceef93ca1ff3db576c5514810d95f192a52f55413ae53bc9958690d945d11` |
| `scripts/refine.py` | `021f2704e30e58f0f379997524dfd5f308eb0c35c541af042d30fc9d25ddaf46` |
| `scripts/replay_refined.py` | `5b87d30775c12b909db7ebb965b1dd2750086a20564e7c8c2cc4ea5f733d6c36` |
| `data/012034-middle5-outer15-certificate.json` | `9d402160d792b5c50de63b22dee90815dd9103a7755fe26cd3bc8d3ec8e54f7f` |
| `data/refine-core0.json` | `d1c8b271154121b94837624db9807d17d778b2c27ca66d802f9a851caa7b5214` |
| `data/replay-core0.json` | `465fdd5862e4d569ebbe1008f0180f484f3ceda6c8938e5e7af3539766c74605` |
| Full CNF | `227d1e5dffb54accfdf81a54624428df35f161a71171bb60562a10446226d880` |
| Original and refined input core CNF | `29be222d0ab948bc0d73e84e1165abb3f406aeeb475fbaf584a492ad2f2d17be` |
| Original trimmed native proof | `8af2e0ffdd001aca85424d43b539cdcbea7d969ea2d76c5fe5c60759961db1cc` |
| Selected refined trimmed proof | `0dcfa83a247c412e33277ab6fe59b30de16d54bb7f2ecd5350a5322939473dc5` |
| `data/witness-audit.json` | `d77a5e1f3e197ee60e89f607c3d0623dfff938f6ce4bec65936bd189e810b49d` |
| `mathematical-note.md` | `3a43229564cf9740382b6eb47d740223febc62457625d1e2d7844ee8e9349d43` |

The successful run and its snapshots are named `SumGeometry117-1793671104407547600`; the initial unlaunched attempt is `SumGeometry117-1793671042394106500`. The earlier native proof, refinement and pending semantic obligations remain preserved separately.
