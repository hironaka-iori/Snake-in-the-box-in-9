# Final document review, round 236

Status: PASS after two short-paper corrections. No remaining blocking finding in the reviewed changes.

## Review coverage and corrections

Read every changed hunk of the main and short TeX originals against their round-236 `data/*.before.txt` snapshots, including the complete new `sec:exchange236`, the abstract, date, verification and bibliography changes, the complete new short-paper section, and all 63 lines of the final `MATHEMATICAL_NOTE.md`. Also read both final Lean sources, their accepted receipts and compiler logs, and the three- and four-exchange audit summaries. This is a bounded review of this revision, not a new full-paper review or proof rebuild.

Two short-paper findings were corrected by the authoring agent before these final hashes were recorded:

1. The deletion rule originally referred to changes on either parity side. An old internal majority vertex can remain selected and become an endpoint, so that general wording was too strong. Lines 734–736 now explicitly concern proposed majority-side changes and old internal minority vertices, which are internal in the candidate if retained.
2. The four-exchange search now explicitly says “exactly four replacements” at line 726. This prevents an at-most-four interpretation.

The earlier inverse-review refinements are present in the final note: the distance-two implication requires the retained vertex to be internal in both paths, and the odd-distance proof handles the distance-nine boundary without an undefined distance-ten coefficient. The main paper's preceding minority-specific discussion and finite even-distance calculation supply the corresponding conditions.

## Numerical results and deductions

The final records match the text:

- `three-audit.json`: PASS_DEGREE_MODEL_AUDIT, required exchange count 3, retained count 93, all 145 bases natively INFEASIBLE, 145 inspected models, zero cycle cuts, no unqueried bases.
- `four-audit.json`: PASS_DEGREE_MODEL_AUDIT, required exchange count 4, retained count 92, base 139 natively INFEASIBLE, bases 7/6/0 UNKNOWN, four inspected models, zero cycle cuts, 141 unqueried bases.

The four-exchange sample is not promoted to a complete cover. UNKNOWN and unqueried cases remain open. No feasible selection or longer snake is claimed.

Independent exact arithmetic gives `145 * binomial(96,3) * binomial(160,3) = 13,879,134,592,000`. The text correctly calls these labelled exchange descriptions before duplicates and does not claim that each was enumerated individually.

Together with the earlier zero-, one- and two-exchange covers, exclusion at exactly three exchanges bounds the candidate minority intersection by 92. The earlier majority intersection bound remains 95. Hence total overlap is at most 187; the old/new vertex counts 192 and 193 imply at least five omissions and six additions. Inverse cube-automorphism transport is valid, with parity allowed to swap. These conclusions retain their stated finite/native premises.

For the restricted family with one complete 96-vertex parity class within three replacements of a saved class, alternation gives at most 192 edges. The top case makes that class the minority class and is excluded by the combined covers. An original seed attains 191 in the included zero-change case, so the stated restricted maximum is correct. No global upper-bound improvement follows.

## Balance and inverse proof scope

The retained-neighbour identity follows from cancelling retained neighbours in the two degree equations for positive-length induced paths. The endpoint exception is retained. The imbalance deletion rule and the distance-two consequence are applied with the needed minority/internal hypotheses. The displayed path extension without deletion remains a valid counterexample to an unrestricted distance-two requirement.

The integer-valued reconstruction formula has the correct coefficients and scale. The finite geometric proof accounts for all distance cases; the independent earlier review checked all ten coefficient values and the expected identity digest. Complete neighbour counts, including deleted and previously unselected minority vertices, are essential. The remaining signed observations must sum to eight or nine according to whether the old minority endpoint is retained. The text does not impose nonnegativity on those individual observations or claim that the conditions suffice for a snake.

The two accepted modules have six reports:

- `ExchangeBalance236`: four implications from Boolean neighbour filters and supplied old/new degree equations. Each reports only `propext` and `Quot.sound`.
- `AdjacencyInverse236`: the five even-distance integer recurrences, reporting `propext`, and finite-list reconstruction under an explicit coefficient identity, reporting `propext` and `Quot.sound`.

The current source, object and compiler-log hashes match both accepted receipts. The main paper and note accurately leave cube distance multiplicities, full labelled-cube instantiation, and native contradictions outside those generic Lean statements. The exact 262,144-entry calculation is separately identified. No performance improvement or novelty claim is made.

Evidence receipt hashes:

- Three-exchange audit: `f5bd12ab1e5739cecb48142e1b2d3f46e36e5a95cd279aa2a93ae6bb3d3abba4`
- Four-exchange audit: `2d2a340e61e859edd5b2f2a76a9e753764a7575f80654ec352d00fdb963966b1`
- ExchangeBalance236 accepted receipt: `a2491aee381d0195e35721d872b32dee8c1fddbaa346b47087bd79f16cfaf16c`
- AdjacencyInverse236 accepted receipt: `03cfadaf461ac32bc0e1c3b5aa1d9cb287a64b324c50a9b61b3c4be230b2d44a`

## Preservation and final hashes

Both authoritative TeX originals are byte-identical to their paper mirrors. Their complete author commands match the before snapshots, preserving Iori Hironaka, Tommy Ma and Steven Zhan in that order. The complete main `hypersetup` block, including metadata, is unchanged. The short paper has no such block in either version. The global interval and independent-rebuild qualification remain unchanged. The short paper and note record the requested pause after round 236.

| Final document | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` and its `E:/Snake-in-a-box/paper/` mirror | 791657 | 12701 | `62ab8ada22a72264685194f7640a2db9cfcb8a19e44f0662f92a4ce096cec4c2` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` and its paper mirror | 48172 | 890 | `3c76fdfc45d560d9f18f10ccd1ca8eda7c0373da42b5c8ea70852c24efec6cc5` |
| `E:/Snake-in-a-box/milestones/236-parity-exchange-frontier/MATHEMATICAL_NOTE.md` | 7817 | 63 | `fc000b081e90498897d829ff880e83b877cfd21320c3233d8b524041117bb9a3` |

No solver, compiler, software test or manuscript edit was performed by this reviewer. This review does not repeat the full native-model audits or rebuild the proof dependency closure. Document compilation and publication are handled by the parent task.
