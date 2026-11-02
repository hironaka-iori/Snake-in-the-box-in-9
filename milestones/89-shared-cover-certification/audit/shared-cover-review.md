# Independent review of shared geometric certificates

## Verdict

No index, box-order, root, truncation or mathematical-scope defect was found in the inspected sources and generated data. All 127 certificate files use exactly the selected class-box order from the pinned milestone 88 payload and exactly the corresponding membership root from milestone 87. The array-based checker preserves the list checker's conclusion through the checked `array_check_eq` theorem.

This review is a bounded source, structure and receipt inspection. It did not run Lean, rerun either generator, or repeat the full pointwise checks. Its evidence snapshot is `2026-11-02T13:05:24.011146+00:00`; compilation status below refers to that snapshot.

## Exact certificate and source comparison

The review independently read all 127 compressed certificate files and compared:

- Each class ID, the entire ordered box-ID list, root and context count against `88/data/box-cover-selected-max-gain.json.gz` and `87/data/coverage-membership-dag.json.gz`.
- Every generated `CoverNNNData.lean` box literal and root against those same source geometries and roots.
- Every generated tree definition against its compressed certificate entry, including accept/reject constructors, reject indices, child order and the final top-level tree reference.
- Every data/check source and compressed certificate hash against the generation receipt.
- Every imported `GraphData.lean` diagram row against the pinned milestone 87 DAG.

All **82,659 ordered box entries** and **152,643 compressed tree nodes** match. Every reject index lies within its class's box list. Every split has exactly six children, in symbol order 1 through 6. Every child references an earlier tree node, and each top-level path has at most six splits. All boxes contain exactly six intervals with endpoints in 1 through 6. No generated source contains `sorry`, `admit` or `native_decide`.

The diagram stores seven entries per nonterminal: depth followed by children for symbols 1..6. Python's `diagram[node-2][x]` and Lean's `nextNode` both use the symbol directly as that row index, so the depth field is not mistakenly used as a child. Every diagram child index is valid. The parser compared all diagram rows, rather than assuming that the imported `GraphData` name identified the intended array. No shadow `GraphData` object was present in milestone 89's first search directory at inspection.

The JSON review receipt records every certificate and generated source hash: `data/shared-cover-review.json`, SHA-256 `7b31f23bf651886802e650d4d2c4dc888768c91e676526ef72c88c305fc418a1`.

## Generation versus mathematical checking

`build_shared_covers.py` pins both upstream payloads, constructs a full six-way tree, and refuses to overwrite a generated file with different bytes. An early accept node requires diagram node 1. An early rejection requires the current prefix to lie in the chosen box and every remaining box interval to equal [1,6]. That is sufficient for the original `coversPrefix` condition. A split extends the prefix by each symbol 1..6 and reduces the remaining depth; failure at depth six prevents an uncovered branch from being generated silently.

The generator independently follows both the resulting tree and the entire diagram for every six-symbol vector. Its saved receipt reports 127 times 46,656, or 5,925,312, pointwise checks. Those checks were read as existing computational evidence and were not repeated in this review. The receipt correctly retains status `GENERATED_ALL_SHARED_COVERS_KERNEL_CHECKS_PENDING`; generation is not successful compilation of the 127 Lean equations.

`check_shared_covers.py` separately pins the generator and its inputs, verifies inherited source/object/log receipts, checks each generated source hash and uses sequential data-then-check compilation. Successful check receipts require one printed theorem with no axioms. Cached results require matching source/object/log hashes and dependency receipt hashes. The script's current module names are `CoverNNNData` and `CoverNNNChecks`; it does not invoke `FastNNNChecks`. Thus the array implementation is currently a separate experimental checking path, rather than an automatic substitution in that runner.

Compressed certificates do not act as trusted Lean input at runtime: generated Lean data are what the kernel compiles. This review establishes that the two representations agree. A hash or a successful data-module compilation alone is insufficient to claim a cover theorem.

## Array/list equivalence

`checkCoverArray` changes only lookup of a rejection box from a list to an array. It retains:

- the same acceptance test `node == 1`;
- a checked bound `i < boxes.size` before the rejection lookup;
- the same default empty box and `coversPrefix` predicate;
- rejection of a split when fuel is zero;
- the exact six-child test and the same recursive calls, prefixes, diagram transitions and child defaults.

`array_check_eq` quantifies over arbitrary diagrams, arrays, fuel, prefixes, roots and certificates. Its induction covers all constructors and identifies array size/getD with the corresponding list operations. It does not assume valid indices, a sorted box list or a well-formed diagram to prove the equality. The guarded out-of-range behavior is preserved as well.

`array_cover_to_list` applies that equality to `boxes.toArray` and uses preservation of the original list under conversion back to a list. Therefore a successfully checked array equation supplies exactly the original `checkCover` equation, without a changed box order, shortened list or extra premise.

`Fast001Checks.lean` states the array equation for the existing `boxes001`, `root001` and `tree001`, then derives the list equation using `array_cover_to_list`. Once its first equation succeeds, the existing `cover_implies_membership` theorem applies with the same six-symbol length, symbol-range and box-avoidance hypotheses. The replacement changes the execution representation, not those mathematical obligations.

## Observed proof status

At the snapshot:

- `ArrayCover-audit.json` reports `PASS_ARRAY_COVER_EQUIVALENCE`, exit zero. Its current source, object and log match the receipt. Both printed theorems use only `propext` and `Quot.sound`.
- `Cover001Data-audit.json` reports `PASS_SHARED_COVER_DATA`, exit zero, with zero theorem audits. This confirms the data module only.
- `Fast001Checks-audit.json` is absent. The presence of its source and empty log is not a successful proof receipt.
- The inherited `Boxes`, `CoverTree` and `GraphData` receipts match their current source, object and log files.

The generic array/list equality is therefore checked. Successful geometric proof for class 1 is not established by the files observed in this snapshot. A later matching receipt may supersede that observation. The existing milestone 88 pilot remains a separate previously checked context; it is not evidence that all newly generated common covers passed.

Even successful geometric equations for all 127 classes would still require the appropriate context-witness validity equations. They also do not identify accepted diagram leaves with exact saved full-key rows or discharge endpoint-column, reference-catalogue, charge or potential obligations. The inherited dependency closure was not rebuilt in this review.

## Reviewed source hashes

| Source | SHA-256 |
| --- | --- |
| `89/scripts/build_shared_covers.py` | `973db7f1368c6b730451f63e0a828b6bb559f9ce7c110461362d6e959291e05b` |
| `89/scripts/check_shared_covers.py` | `59142817589eb20b7c38a074a3f94291a772bdc9bdf32727052c1db24d322a85` |
| `89/lean/ArrayCover.lean` | `24d22edf658a4dfa039f8ec1e2474dfe6cba004350f9180e505c551ab153f14b` |
| `89/lean/Fast001Checks.lean` | `8974673b07860d6682ad9e1d17987c97316c1a475e91b92685d39e1fa3630581` |
| `89/data/shared-cover-generation.json` | `50d207ea1bef01a8b83baa89d8d5f9fd204cfb281c254c9f6092d5aa9ebfb0c6` |
| `88/lean/Boxes.lean` | `4cfdc5590fd95109d68ae36a516f97d0b767c16854fd43396eecc91998c2cc55` |
| `88/lean/CoverTree.lean` | `a965f33fb9cbfa4cde96f4dd4f121ecf356f3e055fbd3cb6d314fd732b18c779` |
| `88/lean/GraphData.lean` | `114c7f9684fbd7fb1e8562fbc73428c79ab5c1c567cd10f7844a536188b9c7b0` |

Pinned upstream payloads:

- `milestones\88-retention-diagram-certificate\data\box-cover-selected-max-gain.json.gz`: `c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93`.
- `milestones\87-retained-array-membership\data\coverage-membership-dag.json.gz`: `5ded4dbe27d3ba795e57e241289facce6444789e30edb9531a312fab58818823`.
