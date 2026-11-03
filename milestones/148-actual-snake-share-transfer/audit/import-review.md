# Import review for the actual-snake share transfer

Status: `PASS_BOUNDED_IMPORT_CLOSURE_AND_SOURCE_OBJECT_HASH_AUDIT`.

The current adapter needs 16 project modules. Its intersection with the milestone147 semantic imports consists of `LocalWindowModel` and `LocalWindowShareModel`. Reuse those two freshly checked objects and rebuild the other 14 modules in milestone148. Their source files total 159,848 bytes; a broad historical build overlay is unnecessary.

The exact dependency closure of `Share146.Semantics147` has 112 modules. Milestone147 checked 113 modules because its batch also includes `Generic147Audit`, which is outside this import closure. The union therefore contains 126 dependency modules, or 128 including the two new148 wrappers. This corrects the preliminary count based on the complete checked batch.

## Source mapping and order

The JSON gives an absolute source path, SHA256, imports and historical object path for each adapter module, plus the full112-module147 source/object/receipt mapping. Its SHA256 is `14592e14439daded334456dca8c57002abf283ad7d8de965e427ec432778df9d`.

Compile these additional dependencies in this order, with `147-countfree-clause-semantics/build` available:

| Order | Module | Preserved source location relative to the repository |
| --- | --- | --- |
| 1 | WindowAutomatonDefs | milestones/73-countfree-share-catalogue/adapter/upstream/WindowAutomatonDefs.lean |
| 2 | WindowAutomatonData | milestones/73-countfree-share-catalogue/adapter/upstream/WindowAutomatonData.lean |
| 3 | WindowAutomatonLemmas | milestones/73-countfree-share-catalogue/adapter/upstream/WindowAutomatonLemmas.lean |
| 4 | Snake9 | work/spectral/.verification/strengthened-n8g3mwjy/core/Snake9.lean |
| 5 | PathStructure | work/spectral/.verification/strengthened-n8g3mwjy/core/PathStructure.lean |
| 6 | WindowAutomatonSequence | milestones/73-countfree-share-catalogue/adapter/upstream/WindowAutomatonSequence.lean |
| 7 | WindowAutomatonBridge | milestones/73-countfree-share-catalogue/adapter/upstream/WindowAutomatonBridge.lean |
| 8 | LocalWindowBridge | milestones/28-direct-share-certificates/upstream/LocalWindowBridge.lean |
| 9 | LocalWindowDirModel | milestones/73-countfree-share-catalogue/adapter/upstream/LocalWindowDirModel.lean |
| 10 | LocalWindowDirKeys | milestones/73-countfree-share-catalogue/adapter/upstream/LocalWindowDirKeys.lean |
| 11 | LocalWindowDirBridge | milestones/73-countfree-share-catalogue/adapter/upstream/LocalWindowDirBridge.lean |
| 12 | DirectionWindowBridge | milestones/73-countfree-share-catalogue/adapter/upstream/DirectionWindowBridge.lean |
| 13 | LocalWindowShareBridge | milestones/73-countfree-share-catalogue/adapter/upstream/LocalWindowShareBridge.lean |
| 14 | CanonicalShareAdapter | milestones/73-countfree-share-catalogue/adapter/lean/CanonicalShareAdapter.lean |

Then compile `ShareTransfer148` and `ShareFromCore148`. The project search path needs the new148 build followed by the checked147 build, plus the existing external library paths recorded in JSON. `SixShapeCoverage` and `ConditionalCatalogueDispatch` are unnecessary.

`PathStructure` imports only `Snake9`, which imports `Std`. `LocalWindowBridge` imports only `LocalWindowModel` and `PathStructure`. The preserved sources for these three modules are byte-identical to their maintained `work/final_lean` copies.

## Shared models and import reduction

Both shared models have identical source bytes and identical compiled object bytes in the old28 and fresh147 locations:

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| LocalWindowModel | 5c374d6b74cbed0ebb91f93e53de21f6e33a85f64532dca6c09f7cefe3a6a8a0 | cdff343e0e81adb26337250528ae18a37d4294b6e00cb7ac77cbe223aa6645e9 |
| LocalWindowShareModel | 3a9210925cbd9432b5c1022c9cd85abff80d8ee008ea8efb53affd75c931f3a3 | deab9f1d3413a3119f23f88e0eee71a7138b6b061c2fa19d0d1fd62605a16c6b |

No incompatible project-module collision was found. The historical maintained path `work/final_lean/LocalWindowShareModel.lean` is absent; the exact checked147 source is available and matches the preserved28 source.

A suitable source-only candidate replaces the adapter's `import Mathlib.Tactic` with `import Mathlib.Tactic.IntervalCases`, leaving all proof bodies unchanged. The latter source and object exist. `interval_cases` at line76 is the only visibly Mathlib-specific tactic in the adapter. The narrower module imports `Mathlib.Tactic.NormNum`, `Mathlib.Tactic.FinCases` and `Mathlib.Control.Basic`.

This reduction must pass compilation before adoption: the umbrella also imports additional simplification lemmas. Eliminating Mathlib entirely while retaining the current `interval_cases` proof body has not been established.

## Evidence and limits

Revalidated the ten relevant historical support sources, objects and logs, and the generic adapter's successful receipt. Revalidated all113 existing147 semantic receipts, including source/object/log hashes, 3,336 explicit dependency-hash references and111 standard-axiom reports. The unused `Generic147Audit` receipt is recorded separately. Mathlib entry-module sources/objects and its manifest are pinned; its full transitive library closure was not audited.

The two new wrappers retain their explicit local-refutation or CNF-unsatisfiability premises. The six directions012301 produce canonical vertices `[0,1,3,7,15,14,12]`; the broad bounds are five copies of `(0,21)`, resolution12 and cap15. The proposed result is share at least16 for either canonical orientation. The wrapper conversions still require compilation, and the unconditional result still requires the complete147 refutation.

No compiler, solver or graph job was launched, and no147 file was modified. Existing historical objects for `Snake9`, `PathStructure` and `LocalWindowBridge` were located; this review does not newly prove their source-to-object compilation. Rebuilding all14 additional dependencies supplies the requested current checked chain.

## Proposed inherited-helper execution

The parent selected a smaller execution plan after receiving this mapping: retain13 inherited project helpers and the two byte-identical checked147 shared models, then freshly check the adapter with the narrower import and the two conditional148 wrappers. This is a three-module fresh check with inherited dependencies. It must not be described as a fresh rebuild of the14 additional dependencies. The complete14-module rebuild order above remains available if stricter provenance is required. No execution or coordinator control was performed by this reviewer.
