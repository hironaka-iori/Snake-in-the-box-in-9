# Remaining actual-snake composition after the share18 replay

Status: read-only source assessment. The161 final contradiction receipt was absent when this note was prepared. No compiler, solver, native worker or graph computation was run. Existing accepted sources and objects were unchanged. This folder's `.gitattributes` contains `* -text` to preserve exact bytes.

## Decision and exact new module order

The old144 `Geometry.lean` and `Reversal.lean` can be copied byte-for-byte into the next composition package. Their source logic and referenced definitions match the accepted159 semantics and148 generic bridges. They still need fresh Lean checks: no accepted144 receipts for `Share144.Refuted`, `Share144.Geometry` or `Share144.Reversal` are present.

After the complete161 contradiction and its saved-evidence audit pass, check these three target modules in order:

1. `Share144.Refuted`: start from the old144 source, change its contradiction import from `LocalWindowUnsat.ShareWindow144` to `ReplayUnsat161`, and qualify the supplied contradiction as `Snake9.ReplayFull161.unsat`. Keep the namespace and theorem name `Snake9.LocalWindow.ShareWindow144.refuted`, and retain the accepted `Share144.Sat` import. Its result remains `RefutedShare window bounds resolution cap` with no contradiction premise.
2. `Share144.Geometry`: copy the original source unchanged. It consumes that `refuted` theorem and the accepted `LocalWindowShareBridge`; it proves the coordinate-labelled forward share18 statement.
3. `Share144.Reversal`: copy the original source unchanged. It invokes `share_bound` on the reversed snake, transports directions with `dir_rev`, and transports the same five-centre share sum with `coreShare_window_rev`.

This requires only the changed refutation wrapper and two unchanged source copies. The old refutation source cannot be used unchanged directly against161: its imported module and unqualified `unsat` name refer to the older144 replay namespace. No mathematical definition changes are needed.

An optional fourth consumer wrapper can use148's accepted `Snake9.CountFreeAdapter73.share_bound_of_either_canonical_match`, supplied by the `CanonicalShareAdapter` module, to express both orientations by canonical direction words. It requires only the fitting window and either canonical match, specializes `K=17`, and uses the completed local refutation. This wrapper is useful for graph-facing consumers; it is not required to complete the two existing coordinate-labelled theorems.

## Definition and theorem compatibility

The159 `Share144.Sat` source is byte-identical to144's original source. Its accepted theorem says that predicates satisfying the exact local share-cap axioms produce a satisfying assignment of the same `Snake9.LocalWindow.ShareWindow144.cnf`. The109-module semantic completion includes104 clause shards, the shared CNF, data/structure, conjunction composition and satisfiability assembly.

The existing definitions remain:

- Window vertices: `[0,1,3,7,6,14,30]`, corresponding to directions012034.
- Five count bounds: all `[0,21]`.
- Resolution12 and forbidden share cap17.
- The same compact13,224-clause CNF used throughout144,159,160 and161.

`Tags.refutedShare_of_sat` takes exactly a satisfiability implication for that CNF and `Unsat` of the same CNF. The proposed161 final theorem has the matching target. There is no map conversion, cap adjustment, count weakening or second interpretation required at this step.

The159 satisfiability receipt and148 share bridge receipt depend on the same `LocalWindowShareModel.olean` bytes: SHA-256 `deab9f1d3413a3119f23f88e0eee71a7138b6b061c2fa19d0d1fd62605a16c6b`. Those files were rehashed and matched. The principal reused source/object/log triples below were also rehashed. Complete transitive dependency auditing remains part of the future composition checker.

The155 final composition supplies a completed contradiction to an already checked actual-snake implication. The same separation applies here, with the additional explicit `RefutedShare` wrapper.155's012032 count-conditioned17 theorem and148's012301-specific wrapper are not inputs to the012034 result. Reuse the generic148 share bridge or canonical adapter, not their shape-specific theorems.

## Final hypotheses and conclusion

For a snake \(P\) with \(m\) edges in \(Q_9\), the forward theorem retains only:

- five pairwise distinct coordinate indices \(a,b,c,d,e<9\);
- a starting index \(r\) satisfying \(r+6\le m\);
- the six transitions \((a,b,c,a,d,e)\) at that index.

Its conclusion is

\[
18\le \sum_{i=0}^{4}\operatorname{coreShare}_{12}(P,r+i+1).
\]

The reverse theorem has the same hypotheses except that the transitions are \((e,d,a,c,b,a)\), and it has the same sum on the original snake. It does not change the five centres. In both statements the universal count bound21 is discharged inside the proof by `coreAlpha_le_21`. There is no additional selected-count, parity, endpoint-location or unproved contradiction hypothesis.

Consequently the selected159 count context \((3,[6,21],4,3,[6,21])\) is covered once the broad theorem passes. It does not need a separate solver query or a new assumption. The reverse-order selected context is \(([6,21],3,4,[6,21],3)\) if a consumer later records it.

## Objects, imports and acceptance gate

Reuse159/build for `Share144.Sat` and its accepted semantic dependency chain;148/build for `LocalWindowShareBridge` and, if used, `CanonicalShareAdapter`;147/build for the local models and tag soundness;161/build for the future completed contradiction and its dependency closure. Preserve160 and the older144/145/146 object paths required by161's receipts.

The new composition build should precede those roots in the search order. Resolve each import to its pinned object and receipt. Preserve the full Mathlib and package search paths recorded in159's `semantic-final-execution.json`: the original `Geometry` source imports `Mathlib.Tactic`. The earlier159 assembly failure showed that omitting package paths can leave `Batteries` unresolved; it was an environment issue and did not require changing the original source.

Before compilation, require the full161 replay audit, the exact final `ReplayUnsat161` source/object/log and axiom report,159's semantic completion, and the reused generic bridge receipts. A pilot or bounded-prefix completion is insufficient. Then audit the three new target receipts in dependency order, including source/checker snapshots and dependencies. Require exactly the three intended theorem reports (`refuted`, `share_bound`, `share_bound_rev`) and only the permitted standard axioms. Inspect both final theorem signatures for absence of an explicit `Unsat` or `RefutedShare` premise. The internal refutation theorem itself is the proved result, not an extra user hypothesis.

If the optional canonical wrapper is compiled, audit its additional theorem and ensure both forward and reversed canonical words are represented. The actual selected centre counts should not be added to the broad final statement.

No new local theorem is claimed by this review. Even successful completion of this composition discharges only the012034 share18 premise; the other local and global certificate obligations remain separate.

## Principal reusable objects

All paths below are repository-relative. Each receipt specifies its complete source, object, log and dependency chain.

| Module | Object | Object SHA-256 | Receipt SHA-256 |
| --- | --- | --- | --- |
| `Share144.Sat` | `milestones/159-share18-proof-continuation/build/Share144/Sat.olean` | `528397fba40b580856803145d607bb916ea3cbf662a4becf1b06a7253cd54a9d` | `440a7f0d0fbfb6411a9ad5d6342d7f1e3f152a72468d9a3d7fa735604ae9c0f9` |
| `LocalWindowTagsShare` | `milestones/147-countfree-clause-semantics/build/LocalWindowTagsShare.olean` | `bec84fd2f84a9d93ed56ac8e4eaf8f446951734be219b41b9f9354bde072d6b8` | `b9785588e6026d0b8c807543ff63d7af21ccb9386fe6a08928a878e3b322b47b` |
| `LocalWindowShareBridge` | `milestones/148-actual-snake-share-transfer/build/LocalWindowShareBridge.olean` | `bc1273784bee500cbb0620c72365f0696d3d7e7d45571c971b0260eff33e4ebd` | `9b8e7298a666664f5c1eb486d6598d3766cf7f055ee08aecf51c600dcd88f16c` |
| `CanonicalShareAdapter` | `milestones/148-actual-snake-share-transfer/build/CanonicalShareAdapter.olean` | `c63a00818911337047f06a1893fecc4c35569c3c797418e543f11c71ee351115` | `cc8d31388c17dbfa640443be4f39c0b3b66c6e61044ff94c69ef56ee44e22f95` |

Receipt paths:

- `milestones/159-share18-proof-continuation/data/Share144.Sat-audit.json`
- `milestones/147-countfree-clause-semantics/data/LocalWindowTagsShare-audit.json`
- `milestones/148-actual-snake-share-transfer/data/LocalWindowShareBridge-audit.json`
- `milestones/148-actual-snake-share-transfer/data/CanonicalShareAdapter-audit.json`

## Inspected source and evidence hashes

| Path | SHA-256 |
| --- | --- |
| `milestones/144-countfree-share18/lean/Share144/Refuted.lean` | `d726e920d039f3e94fb1ef473d0f95a22a265d54da08a7c3c2f3b3f4e0c22362` |
| `milestones/144-countfree-share18/lean/Share144/Geometry.lean` | `5358fed5cabd2d1161f1268805f534494bdd6341cba8ffd9009e834ebaa6bac0` |
| `milestones/144-countfree-share18/lean/Share144/Reversal.lean` | `7552de4acedefa31a48cc888f989ffef3734fb48ebdb99bc661a2707163cf26e` |
| `milestones/144-countfree-share18/lean/LocalWindowCnf/ShareWindow144.lean` | `1fa19f9fa0fe21ef77240a2572eee3a8dfd8c886cfd8359341415bd59b0320ad` |
| `milestones/159-share18-proof-continuation/lean/Share144/Sat.lean` | `06a3c7d8191767eb6cccb6d0f78116c4792d0c04c613ab215a0e19e47bc726a3` |
| `milestones/159-share18-proof-continuation/data/semantics-completion.json` | `3e467570d8987e7fc0f72b5d96e0e35bc6f8a4101a1d583e49af1b15b0c631d9` |
| `milestones/159-share18-proof-continuation/data/semantic-final-execution.json` | `d497469356f8666ae057d8f017d74863bcd6a7f9a09ab4b86d1d0c73b5b6f94c` |
| `milestones/148-actual-snake-share-transfer/lean/LocalWindowShareBridge.lean` | `8b2d06a67664f7d9ded4d0b3422e8cf73c151caed2a0cc08772ec74cf7d59ca8` |
| `milestones/148-actual-snake-share-transfer/lean/CanonicalShareAdapter.lean` | `fc2aced85e8b3159ea65f750e7e3d64716284d650f354848b62af640768d3cc2` |
| `milestones/148-actual-snake-share-transfer/lean/ShareFromCore148.lean` | `a7ec4a5b0c0033bb6c9548d9d5c2598ff4c3dfa097c4c400fe0ea3c6cdf57597` |
| `milestones/155-share17-replay/lean/ShareComplete155.lean` | `3652fbffbd7977553308f05a744d3a0c88c3fe0ec1d2206291691e0726fe160b` |
| `milestones/161-share18-full-replay/data/full-source-plan.json` | `25e0df484f25b9276aecd0f6fd29d71ce299cc738dac2a8ec6d8dfd7c1892fc3` |
| `milestones/161-share18-full-replay/lean/ReplayUnsat161.lean` | `f74ff40851e3461a3a412890d4ac5418667ae84db3f5a558ddd05a8744d233f5` |
