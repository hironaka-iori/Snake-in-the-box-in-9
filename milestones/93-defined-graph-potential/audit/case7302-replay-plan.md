# Case 7302 isolated replay plan

Bounded read-only audit, 2026-11-03. No proof source, object, replay data or case record was changed; no compiler, solver or process-management action was launched. Only this report was written. The parent reports that the approximately 14 GB orphan has been stopped; this review did not independently measure that process.

## Smallest useful next compile

Create one new pilot module outside the case tree, for example `93/lean/Replay7302/Segment001.lean`. Import only `LocalWindowUnsat.ShareWindow7302.Data1`, which transitively imports `Data0` and the existing checker. Preserve `maxRecDepth 100000`, `maxHeartbeats 0` and `Elab.async false`. Under a fresh helper namespace, prove exactly

```lean
theorem segment001_checked : check start1 proof1 = true := by
  decide +kernel
```

Open the original case/checker namespaces and print this helper's axioms. Use fresh output and log paths and a separate pinned receipt. Leave the existing `Check1.lean` unchanged during this pilot. Run only this one compile after the parent has verified that a slot is free. This measures whether the first segment alone completes; it is not evidence in advance of lower memory use or shorter runtime.

The original `Check1` has six decisions with asynchronous elaboration disabled. Its timeout log does not contain per-declaration completion markers, so the review cannot determine whether it stopped in `ok1`, a later check, or checkpoint conversion. No claim that the first segment is the unique bottleneck is justified.

## Exact current data and dependencies

The selected LRAT has 389,216 lemmas, 25,783,817 hints, 27,815 slots, 858 segments, 214 checkpoints and 15-bit words. Its CNF hash is `b9244dfd2079453bcc79855ef63401336a71c25f7b12c30d0d8d2c63a32ef2f1`; selected LRAT hash is `4af69d71a1e495c7b8bc5d7df9adbbf7f159e9d74dcb4fc6082e7afa9cb77ece`. This plan changes neither. The selection receipt says the semantic sources were unchanged by slicing.

Current replay sources reside at `73-countfree-share-catalogue/cases/case7302/lean/LocalWindowUnsat/ShareWindow7302/`. The first dependencies are:

| Data module | Imports within the case | Important definitions |
|---|---|---|
| `Data0` | `LratFastOffset8192W15`, original compact CNF module | `inputSlots`; `start1 := loadRaw (perf 15 0) raw inputSlots` |
| `Data1` | `Data0` | `proof1`; `start2 := replay start1 proof1` |
| `Data2` | `Data1` | `proof2`; `start3 := replay start2 proof2` |
| `Data3` | `Data2` | `proof3`; `start4 := replay start3 proof3` |
| `Data4` | `Data0` | `proof4`, checkpoint `cp5`; `start5 := build 15 cp5` |
| `Data5` | `Data4` | `proof5`; `start6 := replay start5 proof5` |
| `Data6` | `Data5` | `proof6`; `start7 := replay start6 proof6` |

The six segment hint counts are 30,101; 30,016; 30,135; 30,076; 30,020; and 30,071. These count hints, not peak kernel memory or list lengths. The generated `proof1` source is much longer than some later segments despite similar hint totals, so segment hint counts alone are insufficient for scheduling.

`Check1.lean` imports `Data0` through `Data6`. It proves `check startN proofN = true` for N=1,2,3,5,6. Its fourth statement is stronger:

```lean
theorem ok4 :
    andB (check start4 proof4)
      (cpOk (replay start4 proof4) start5) = true
```

The main `LocalWindowUnsat/ShareWindow7302.lean` uses `ok1`–`ok3` through `replay_true`, uses `ok4` through `cp_true`, and then resumes ordinary replay at `start5`. The checkpoint condition must remain. The same pattern recurs every four segments, with the final segment also checking the empty clause.

At inspection, `completion-record.json` ended with the current-source-matched `Check1` timeout after 900.437 seconds. No `Check1.olean` existed. `Check2` had no successful record or object. `Data0`–`Data6` and both checker support modules had current-source-matched successful records and existing objects. Their direct dependency source hashes match the inspected data chain. This was a narrow dependency check, not a complete audit of every prior module or object. The older resume script's starting message names `Check66`; it does not describe the latest failure, which the completion record identifies as `Check1`.

## Reproducible split preserving all six statements

If the pilot is useful, generate independent helper modules from the original `Check1` declarations, with fresh helper theorem names. Each should copy its exact proposition and kernel proof command and print the resulting axioms. Minimal imports are:

| Helper | Sufficient direct data imports |
|---|---|
| segment 1 | `Data1` |
| segment 2 | `Data2` |
| segment 3 | `Data3` |
| segment 4 | `Data3` and `Data4` |
| segment 5 | `Data5` |
| segment 6 | `Data6` |

Segment 4 needs both branches because `Data4` imports only `Data0`; it does not supply `start4`. If the combined checkpoint statement is itself problematic, its two Boolean equalities can be checked in separate processes and the exact original `andB ... = true` recovered by rewriting both results to `true`. This would yield seven helper decisions for this group, with the original six public propositions preserved.

After successful helper checks, replace only `Check1`'s proof bodies with references to the helpers and add their imports. Keep the public namespace, names `ok1`–`ok6`, and proposition text identical. The main refutation source can remain byte-identical because it imports `Check1` and uses those same declarations. Helper names must differ from the public names; importing two independent declarations with the same fully qualified name would cause a conflict.

For integration, either place the approved helpers in the case's source tree so the existing dependency discovery sees them, or extend the final audit explicitly to pin helpers outside that tree. The current auditor intersects imports with its local source set; outside helpers must not become untracked support. Do not silently copy a pilot object into the old module path.

The existing generator `10-window-aggregate/scripts/gen_lean_lrat.py` has a `group` parameter, currently six. Changing it to one and regenerating globally would renumber all `Check` modules and change the main import list. That is broader than necessary for the first diagnostic. An additive per-group helper transformation preserves current data and unrelated successful checks. It should read the pinned original source, extract each complete proposition, validate the expected six names, emit deterministic helpers/wrapper, and save a manifest of original and new source hashes and theorem signatures.

## If one decision alone remains too large

Splitting a file only isolates process lifetimes; it does not bound the normalization cost of one `check`. If segment 1 alone fails under the chosen limit, stop before expanding the split across all 858 segments.

A second-stage option is to partition the original `proof1` list into literal sublists, prove their concatenation equals the unchanged original list, and prove a generic `check_append` composition theorem. Intermediate states must be the exact replay states. The checker uses `ins` in `check` and `ins'` plus `seqT` in `replay`; these are related by existing `insertF_eq`, `insertF'_eq` and `seqT_eq`, as already used inside `replay_true`. They are not a reason to assume the append equation without proving it. No ready `check_append` theorem was found in the inspected checker.

Keeping intermediate states as replay expressions may still recompute large prefixes. Explicit cached trees would need proved exact correspondence, or an appropriately proved checker-preservation theorem. The existing `cpOk` alone preserves clause truth for semantic refutation; it does not assert equality of the old and new trees and does not immediately recover the original Boolean `ok1` proposition. Regenerating checkpoints or changing segment cuts is a different replay export and would change more data and downstream dependencies. It should be deferred until the isolated measurement establishes that a within-segment change is necessary.

## Preservation, reuse and controlled restart

The pilot adds source/object/log/receipt files only under its own milestone paths. For the later wrapper split, changed artifacts are the new helper sources and objects, the `Check1` source/object/log/receipt, and manifests describing that changed source closure. The CNF, selected LRAT, checker definitions, input slots, all `Data` modules, semantic modules, and unrelated completed `Check` modules remain byte-identical. Their successful work remains reusable after validating exact source, dependency and object provenance. Do not mark a module complete from its filename or object existence alone.

The main refutation and geometry theorem sources may remain unchanged, but their successful compilation must use the new checked dependency closure. Any existing descendant object depending on the replaced `Check1` object must be rebuilt or validated through a dependency-aware receipt. The current `complete_share.py` resume criterion records direct dependency source hashes and only tests object existence; it is not a recursively hashed object-provenance certificate. A new pilot/integration runner should pin imported source and object hashes, verify them before and after compilation, and record the exact search-path order.

Preserve the original timed-out source, log, completion record, selected-source archive and export manifest as historical evidence. Publish new split-source/archive manifests rather than rewriting the selected export receipt as if the helper transformation were part of the original exporter. The public theorem statements and selected proof data stay the same, but the proof-source closure has changed and must be identified accurately.

The timeout was applied to a `lake.exe` launcher through `subprocess.run`; the reported orphan demonstrates that stopping the launcher was insufficient in this run. The next runner must record the launcher and descendant identity, use an exclusive replay lock, and retain that lock whenever child completion is uncertain. A Windows job object or verified descendant-tree cleanup can enforce a timeout across the launched process tree. Do not restart automatically based solely on a parent timeout. A direct `lean.exe` invocation would also require preserving the resolved environment currently supplied by `lake env`; it should not be substituted without checking those imports.

Record elapsed time, peak private bytes or working set with its measurement definition, concurrency conditions, exit code, source/object/log hashes and theorem axioms for the single pilot. No speed or memory reduction is asserted before a comparable measurement. A successful isolated segment is partial replay evidence, not the final share-20 theorem.

## Exact source pins

Paths below are relative to `73-countfree-share-catalogue/cases/case7302/` unless stated otherwise.

| Source | SHA-256 |
|---|---|
| `lean/LocalWindowUnsat/ShareWindow7302/Check1.lean` | `7aef76306999ebf3c6b6835007f9655149aabeb6d3246e2abf80a5d7594bec6a` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data0.lean` | `43ad175d1e1e0f3b4ccd7045b9c4e94578a3317629a7f0ff3ec2f3d29f81a652` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data1.lean` | `54cd73bf812a13f211c7a6fc7d40cdaed94aaf0677ba645997260106597e0517` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data2.lean` | `076c1ec3502cdb2174f403b8ccde75cdd8babdae44fc821a705a13ce10c91593` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data3.lean` | `ff665500c7b9bea084fa4c2ee0cbef03a5cffa8b4fd0931e24015e75676b16c2` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data4.lean` | `1e9c3075f3fb1372cbba0ee6e115117cd0217847e60bbb340b8a21537fbfec6a` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data5.lean` | `14f41b401139750e6af03b48953fe6e4fad26f268e96b2af0797cdd50cb7d8b2` |
| `lean/LocalWindowUnsat/ShareWindow7302/Data6.lean` | `b73018eba216a9b89d8f3bafbb0b91384b0ea0e1f05316f5b5e21b56f8784897` |
| `lean/LratCheckOffset8192.lean` | `fb00bda06881f894fb3d272ed7236e3bd91ba0fd919186a71f0618a5630578c4` |
| `lean/LratFastOffset8192W15.lean` | `f89681bcddd6b3c6363400e4e8fe27aeb1b7d3384f57643247b30cc97f04c0f1` |
| `lean/LocalWindowUnsat/ShareWindow7302.lean` | `cf698d5b9dc72376a7675047f98a697aea3c4c249a4e1911453439c9e4212bd0` |

The completion-record snapshot used here had 658 rows and ended with the `Check1` timeout. Its earlier successes are historical module records, not a count of currently completed distinct selected-proof modules. No broader completion claim was made.
