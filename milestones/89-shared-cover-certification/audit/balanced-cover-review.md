# Balanced cover review

## Verdict and scope

No concrete indexing, ordering, truncation, split-size, default-value or theorem-scope defect was found in the reviewed balanced-table path. This is a bounded independent source/data review. No Lean process, solver, generator or full count-code replay was launched, and the active class 1 proof job was not touched.

The receipt snapshot is **2026-11-02T13:14:10.124788+00:00**. The machine-readable record is `data/balanced-cover-review.json`. The earlier `shared-cover-review.md` and its receipt were preserved unchanged.

## Exact literal comparisons

An independent recursive-descent parser read every `Table.empty`, `Table.leaf` and `Table.node` constructor directly from the generated Lean sources. It did not import or execute either generator. Every token in each literal was consumed; constructors, numeric arrays and six-interval boxes were parsed explicitly.

All 127 box-table flattenings match both the selected geometry order in the pinned milestone 88 common-cover payload and the existing `boxesNNN` Lean lists. They contain **82,659 leaves and 82,532 internal nodes** in total. Every node stores its exact left leaf count; every split divides its leaves into floor-half and ceiling-half. With a leaf at depth zero, every table has maximum depth exactly `ceil(log2(number of leaves))`, which is **9 or 10** for these tables.

The graph table has **3,981 leaves and 3,980 internal nodes**, with depth **12**, also equal to the ceiling of the base-two logarithm. Its flattening equals both the pinned milestone 87 DAG rows and all original `GraphData.lean` rows, including the leading depth field. Graph lookup uses `node-2`; symbol 1 selects row position 1, so the leading field is not mistaken for the first child. Constant nodes 0 and 1 retain their original behavior.

The review additionally tested **88,944 table lookups**: every in-range index and 18 out-of-range indices per table, including a large index. It checked **43,857 graph-advance evaluations**, including node and symbol boundary/default cases. All comparisons passed. The generic theorem, rather than these finite tests, supplies the all-index claim.

All 256 generated balanced sources match `balanced-cover-generation.json`. All 127 class IDs, roots, literal box counts and the statements of `originalCoverNNN` match their intended classes. The 127 original data-source hashes and compressed certificate hashes also remain identical to the earlier independent review, which compared all **152,643 compressed tree nodes** against the Lean literals. Thus this representation change does not replace or reorder the original cover trees.

The first read-only audit attempt used an insufficient regular expression for a multiline original box list and stopped with a parser error. The parser was corrected to delimit the complete box definition by the following root definition. This was an audit-code error; it produced no artifact and identified no source-data defect. The successful receipt records it.

## Generic equivalence and written conclusions

`BalancedLookup.Valid` requires each stored split size to equal the length of the flattened left subtree and recursively validates both children. It does not itself assert balance. `check_iff_valid` connects its Boolean check to this condition. `lookup_eq_getD` proves equality to flattened-list lookup for **every natural index and every supplied default**, including empty tables, leaves with positive indices and indices beyond the entire table. The subtraction on a right branch is guarded by the complementary comparison, so truncating natural subtraction introduces no missing case. `lookup_eq_list` transports that conclusion through the exact flattening identity.

`LookupCover.lookup_check_eq` preserves the complete original recursion. It retains the box-count guard, default box, six-child guard, prefix extension by `j+1`, child default, node acceptance condition and fuel-zero rejection of a split. Its explicit hypotheses identify the box count, every box lookup and every graph transition. No domain restriction on the indices is inserted. `lookup_cover_to_original` therefore concludes exactly the original `checkCover g boxes 6 [] node certificate = true` equation.

The generated `advanceBalanced_eq` supplies all-node/all-symbol transition equality using the graph flattening theorem and the same empty-array/zero defaults. Each written `originalCoverNNN` supplies the exact original box count, the all-index `lookup_eq_list` equality, this graph equality and the concrete balanced cover equation. Its conclusion is exactly the corresponding original checker equation on `retainedDiagram`, `boxesNNN`, `rootNNN` and `treeNNN`.

Once those concrete statements pass Lean, the existing `cover_implies_membership` theorem applies with its unchanged six-symbol length, symbol range 1 through 6 and avoidance of every selected box. Neither this equivalence nor a geometric cover alone supplies the context-specific proof that all selected boxes are forbidden.

## Runner and proof status

`build_balanced_covers.py` pins its source payloads to the earlier generation receipt, preserves selected box order and refuses to overwrite a generated file with different bytes. Its reported status explicitly says that kernel checks remain pending.

`check_balanced_covers.py` validates the selected class IDs, generator/input hashes and current source/object/log receipts for the inherited dependencies. It checks exact generated source hashes before compiling, records dependencies, preserves an earlier log, writes a fresh object and promotes it only after successful compilation and audit inspection. Concrete validity, flattening and balanced-cover equations are required to have zero axioms. The transported original equation may use the permitted standard axioms inherited through the generic bridge. Reuse of an ordinary `CoverNNNData` receipt has an explicit earlier-driver exception to dependency-map equality, while its source/object/log bytes and the currently used core dependency receipts are still verified.

At the snapshot:

- `BalancedLookup` has a matching successful receipt with **five** printed audits, each using only `propext`.
- `LookupCover` has a matching successful receipt with **two** printed audits, using only `propext` and `Quot.sound`.
- `BalancedGraphData` has compiled successfully, with **zero theorem audits**.
- No successful receipt was present for `BalancedGraphChecks`, `Balanced001Data` or `Balanced001Checks`.
- No successful receipt was present for the old `Cover001Checks` or `Fast001Checks` experiments. The saved stop record says they were stopped without a successful cover result. Their elapsed times of approximately 11.4 and 7.9 minutes are stopped-run observations and do not establish a completed-check speed comparison.

These observations are timestamped; a later matching receipt can supersede the pending status. No claim that the concrete class 1 cover or all 127 covers passed follows from this review. Generic balance/performance is also not a theorem of `BalancedLookup`; only the particular generated literal depths were checked here. Exact saved-row membership, endpoint columns, context witnesses, reference-catalogue closure, weights, potential inequalities and a global snake bound remain separate obligations.

## Exact reviewed hashes

| Source | SHA-256 |
| --- | --- |
| `scripts/build_balanced_covers.py` | `ef1de3ce2ec799fceaf09e2ab66f93e1ecb30bb250f666d4f08522aeeb0fe1b6` |
| `scripts/check_balanced_covers.py` | `18eff75f81cef41c0dcefc4fd2e6fcc8d5a92e17d929beac7828f4c76dd264fa` |
| `lean/BalancedLookup.lean` | `b956f192953c15554de5c74dbcd946bcabda4c2d392f85b5b65d965f07fe5f2e` |
| `lean/LookupCover.lean` | `f3f82a8c19560592c7c37843c02e643f97d7375420f10aa637f2b75d70cc8097` |
| `lean/BalancedGraphData.lean` | `f33c950d96a47d6d6305ad1842a4a10a389bf84712322bcb207f3f800935343c` |
| `lean/BalancedGraphChecks.lean` | `72481ceee07f82067a334bdbd7d8e7e7dee4d4009437c7b60b08e1de5e49d963` |
| `lean/Balanced001Data.lean` | `0809642d0d3cd0b1f98cef341f4eefa3c727e0e052f2c2b7fde87b3755f07193` |
| `lean/Balanced001Checks.lean` | `5d91db361846aaa642b43b1decb1fc74d62c5d868a04091a9bdef40cb726d60e` |
| `data/balanced-cover-generation.json` | `58dfd0f7b59c672346dbf9c8705112bff1600715a1498f81d5c0b10e550814ee` |
| `data/lookup-benchmark-stop.json` | `c80c7d6dd3c4bf3e31062652dd68825cc98be563aa46a26c1e1220f7c948d4c5` |

All 256 generated source hashes, per-class roots/counts/depths, upstream payload pins and checked dependency source/object/log hashes are recorded in the JSON receipt.

- Balanced review receipt: `5f50b50c70698455e20011cd9550b75875d10f44d3868f1c0f0dff279561fe02`.
- Earlier shared-cover review receipt, unchanged: `7b31f23bf651886802e650d4d2c4dc888768c91e676526ef72c88c305fc418a1`.
- Milestone 88 common-cover payload: `c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93`.
- Milestone 87 DAG payload: `5ded4dbe27d3ba795e57e241289facce6444789e30edb9531a312fab58818823`.
