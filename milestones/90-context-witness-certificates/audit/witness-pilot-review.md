# Witness pilot review

## Verdict

No concrete metadata, order, index, guard or theorem-scope defect was found. The bounded review independently parsed the generated balanced tables and both witness lists, compared them with the original Lean/source payloads and the 507-job plan, and inspected the generic substitution and class 1 membership argument. No compiler, solver, generator or full validity replay was launched.

The proof-status snapshot is **2026-11-02T13:32:14.056291+00:00**. The exact hashes and checks are saved in `data/witness-pilot-review.json`.

## Exact table and list checks

The complete `directionTable` literal flattens to the **505** directions in milestone 77 `DirectionTables.extensions`, in precisely the same order. Its 504 internal nodes have correct stored left leaf counts; its maximum depth is **9**. The complete `referenceTable` literal flattens to the **1,378** reference keys in milestone 85, reconstructed independently from the ordered 22 `ReferenceChunkNN` source lists and their `ReferenceUnion.referenceKeys` concatenation. It also agrees with `reference-union.json`. All 1,377 stored split counts are correct and maximum depth is **11**. Both depths equal the ceiling of the base-two logarithm of the leaf count.

The parser consumed every literal token. It was independent of the generator's rendering function. A further **1,901** finite lookup comparisons covered every valid index plus boundary and large out-of-range indices, with the respective defaults `[]` and `([],[])`. Every comparison passed. The generic all-index theorem supplies the unbounded-index result; these computations are additional checks only.

Both generated witness lists were parsed constructor by constructor, including rule index, offset and reverse flag. List 1 and list 3 each contain **640** entries and agree exactly with the pinned milestone 89 materialization. They contain no history constructor. The six generated assignments are:

| Direction | Original witness list | Plan base job ID | Entries |
| --- | --- | --- | --- |
| 1 | 1 | 1 | 640 |
| 3 | 3 | 3 | 640 |
| 307 | 3 | 309 | 640 |
| 308 | 3 | 310 | 640 |
| 310 | 1 | 312 | 640 |
| 312 | 3 | 314 | 640 |

These are exactly the six class 1 contexts in the original payload and job plan, all at source history zero, with **3,840** validity occurrences. The imported `boxes001` list also matches every original class 1 geometry ID in order. Thus each generated zip has both lengths equal to 640. Sharing two data lists does not merge the six direction-specific validity obligations.

## Preserved guard and lookup semantics

After replacing the supplied lookup/count expressions by their originals, the normalized bodies of `referenceBoxValidAt` and `boxWitnessValidAt` are textually identical to the original definitions. In particular:

- The outer box length, history bound and direction bound remain `b.length = 6`, `q < 75` and `di < 505`.
- Reference key range, minimum symbol length, placement upper bound, offset `s+2`, canonicalized oriented direction slice and both singleton endpoint equalities remain unchanged.
- The short-rule and interval-rule validators are called unchanged, preserving their placement, orientation, saturation and interval tests.
- The history branch still calls `historyBoxValid q (extensions.idxOf ds) b ki`. It does not silently replace the decoded direction index by `di` or by a new lookup-table index.
- The generic replacement requires lookup equality for every natural index and the exact reference count. Defaults beyond the source table are therefore identified explicitly.

`WitnessLookup` proves function equalities for reference, individual and whole-list validators under these hypotheses. It neither removes a guard nor introduces an extra assumption about actual histories. `WitnessTablesChecks` is written to supply the exact flattening identities, valid split sizes, count equality `1378 = referenceKeys.length`, and all-index lookup identities through `BalancedLookup.lookup_eq_list`.

The generators preserve list order and refuse to overwrite differing generated Lean data. Their saved source, payload, input and generator hashes match the reviewed bytes. The class generator pins the milestone 89 payload and checks the exact six directions, history-zero contexts, two list IDs, lengths and absence of history witnesses. Its source-generation status is separate from proof completion.

## Exact scope of the class theorem

The written `class001JobValid` checks witness length before the zip, checks that every zipped witness is history-free, and checks optimized validity at history zero. The proof of `class001_numeric_membership` extracts those three facts, transfers optimized validity to the original validator by function equality, and invokes the previously checked history-free transport and geometric cover.

Its hypotheses are membership of `(di,ws)` in the six listed jobs, any `q < 75`, `code < 46656`, and the original `numericKeep q di code = true`. Its conclusion is acceptance of `digits code` by `retainedDiagram` at **root001**. The source contexts being at history zero does not restrict the written theorem to history zero: history-independent witnesses are transported at the same direction, while the original numeric predicate retains its history guards.

This is a one-sided acceptance implication. It does not assert that every history/direction pair is compatible, that root001 is the exact saved block for every such pair, that every accepted diagram value is numerically retained, or that every actual snake satisfies the numeric predicate without the separate retention hypotheses. It supplies no saved-array row, endpoint, weight, potential or global snake-bound theorem.

## Receipt observations

At the recorded snapshot, current source/object/log hashes matched successful receipts for:

- `WitnessLookup`: **four** printed audits. The three equality results use only `propext` and `Quot.sound`; the generic membership result additionally uses `Classical.choice`.
- `BalancedLookup`: **five** printed audits.
- `Balanced001Checks`: **four** printed audits, including the original geometric checker equation.
- `SharedAssembly` and `ContextTransport`: **four** printed audits each.

No successful receipt was present for `WitnessTablesData`, `WitnessTablesChecks`, `Class001WitnessData` or `Class001WitnessChecks`. Thus the concrete tables and witness pilot were generated and reviewed, with their Lean checks still pending in this snapshot. Later matching successful receipts can supersede that observation. This review did not rebuild the inherited dependency closure.

## Reviewed source hashes

| Source | SHA-256 |
| --- | --- |
| `scripts/build_witness_tables.py` | `6b282c5c9380c1b1740cacafe1813696a7855019868f83947bc50d838829a97f` |
| `scripts/build_class001.py` | `d3ff7208a5ec898b2fe5a5758ac7347c8be4b5771b8c7fdcd01a482382497635` |
| `lean/WitnessLookup.lean` | `f04f07ffd5b21fb03d307faf447df93068646a0dee786e6df1bc604952806076` |
| `lean/WitnessTablesData.lean` | `cf49eb39d4fa6c531d79f3bf9eac0f94eeea02c20b3e660d77d135acee327ca9` |
| `lean/WitnessTablesChecks.lean` | `cdd98f0f0b8b2e07d61cb34527b46f0b3b0d13c4661774db5945973865f92d6b` |
| `lean/Class001WitnessData.lean` | `c41e402284c4846cfef43cd5608e47326e79f93c597beb67a471eecac67d542d` |
| `lean/Class001WitnessChecks.lean` | `e377af490b0bd03f0666b480df3a6dd71417ac9529bb479d776ec1d070bb2cab` |
| `data/witness-table-generation.json` | `9200aa32c74a496350e4e5a4f3ef8ba80647e39a753de6dabdf5c2e584013c21` |
| `data/class001-generation.json` | `fb8538d636861efb1ce5fb0f4ce408bd6439132f3396a878ee7d48d783ff3e0e` |

- Full review receipt SHA-256: `21c028fe41408da00f23ac8a3a55665a57578bc80681a3699c03034f0211b341`.
- Pinned witness payload: `5dd985dc9e31441f481881895a827b7d88d68864b5104f07483adaaf86932d51`.
- Pinned 507-job plan: `68ae7c1c81d6c714a63964c5859d0e8b3cfaa93bf7a30569252dcb22bd9f376c`.
- Generic `WitnessLookup` receipt: `b6e78a765bcfafb3f86b8bf0c45ee87a72efa8c706c2e595728449d8881bd8bb`.
- The JSON receipt records all 22 reference chunk hashes, the original direction and box sources, generated payloads, and observed source/object/log receipts.
