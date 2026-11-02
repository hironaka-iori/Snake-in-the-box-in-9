# Closure runner review

Bounded read-only source review, 2026-11-02. Reviewed `scripts/build_closure.py`, the final-assembly and memory-gate changes in `scripts/check_batch.py`, and `data/checker-revisions.json`. No compiler, generator, solver, or process-management action was run. Only this report was written.

## Verdict

The three material findings raised during review are resolved in the final inspected checker. The final assembly has an appropriate dedicated success status; source and direct dependency pins survive the wait boundary; interrupted active work conservatively retains the runner lock. No remaining proof-scope or dispatch defect was identified in this bounded review. Closure generation and compilation remain pending, so this verdict concerns the runner source rather than completed all-class theorems.

The remaining minor wording issue was resolved in the final narrow follow-up. The general run-record `scope` is now updated at `PASS_ALL_CLASSES_AND_NUMERIC_DIAGRAM` to state that all 127 class proofs and source-compatible context assignment establish numeric diagram acceptance, while exact saved rows, endpoint columns and actual-snake reference premises remain separate. Comparison with `data/repairs/check-batch-before-final-scope.py.txt` found exactly this one added assignment. No further defect was identified in that delta; no compilation or broader re-review was performed.

## Findings resolved during review

1. **Dependency changes across a wait.** The first memory-gate version captured dependency receipt/source/object/log hashes before waiting and subsequently rechecked only the current source. The final checker rechecks the complete direct dependency pin map immediately after the wait and again after `proc.wait()`, before publishing a successful receipt. Both maps must equal the captured map. Current source bytes are checked before dispatch, after waiting and after compilation. The earlier version is preserved in `data/repairs/check-batch-before-dependency-recheck.py.txt`.

2. **Lock removal after interrupted compilation.** The earlier `finally` could remove the runner lock while an interrupted child remained alive. The final source saves `active` with `PREPARING_LAUNCH` before opening the log or launching a child, records the launcher PID after launch, and clears `active` only after successful checks and receipt publication. The owned lock is retained whenever an active/preparing module remains. An interrupted or failed module therefore requires actual-process inspection before restart, even if its child has already ended. No child-tree termination is claimed and none was attempted. The earlier version is preserved in `data/repairs/check-batch-before-lock-retention.py.txt`.

3. **Final-module success scope.** `CloseBatch` now receives `PASS_NUMERIC_DIAGRAM_FAMILY`, with the scope “Combines all127 concrete class memberships with the checked context assignment. Saved-row and endpoint interpretation remain separate.” The full run receives `PASS_ALL_CLASSES_AND_NUMERIC_DIAGRAM` only after this module returns successfully. Other class/data receipts retain their narrower scope.

## Assembly and preparation checks

`build_closure.py` iterates exactly `range(127)`, pins each original `WitnessNNNChecks.lean` against `batch-generation.json`, and records the current `ContextAssignmentChecks.lean` source hash. Its generated import set and 127 case branches cover the entire class domain. `retained_class_family` applies each corresponding `classNNN_context_membership` with the original context-membership, code-bound and numeric-keep hypotheses; the extra unused history bound is harmless. The second theorem applies `numeric_context_membership` to that full family and retains `di < 505`.

The generator reports `GENERATED_PENDING_ALL_CLASS_PROOFS` and expressly makes no completed theorem claim. It refuses to overwrite different `CloseBatch.lean` bytes. The runner pins the generator, all closure inputs and the expected final source hash. It schedules `CloseBatch` only after iterating the exact ascending class list `0,...,126`, with direct dependencies on `ContextAssignmentChecks` and all 127 class checks. Compiler or audit failure prevents the final successful run status. Source changes, missing receipts and changed direct dependency pins fail closed.

At the final source snapshot, `data/closure-generation.json` and `lean/CloseBatch.lean` were absent. The parent explicitly reports generation is deferred until the assignment source is stable. The runner reads the closure manifest before acquiring its lock, including for selected-class runs. Thus running the closure generator is a required preparation step before starting this runner version. The absence is a pending preparation dependency, not a false success. The active-pointer record inspected referred to the earlier completed three-class pilot with terminal `PASS_SELECTED_DIRECT_WITNESS_CLASSES`; it provides no evidence of an active full batch or completed closure.

## Waiting, publication and limitations

During ordinary execution, the exclusive `witness-batch.lock` spans the runner. Geometry waits and memory waits launch no Lean process. Each compiler launch is followed by `proc.wait()` before another module can be dispatched. The added waiting path therefore does not itself duplicate jobs. A pre-existing lock is rejected rather than automatically treated as stale. Per-run temporary object names and atomic publication preserve the previous completed object until a new check succeeds. The final interrupted-work rule additionally prevents automatic restart while child completion remains unverified.

The memory control is accurately documented as a pre-launch observation. It sums private committed bytes of visible `lean.exe` processes, waits in 15-second intervals, and clears the wait state when the threshold permits dispatch. It does not reserve memory, bound the new job's peak, limit all machine processes, or prevent another independent launcher from starting after the observation. No memory-performance result was measured here.

Successful receipts require compiler exit zero, no reported `error:` or `sorryAx`, no prohibited source proof shortcut, exactly the expected printed theorem audits, and only the allowed standard axioms. Full closure expects two audits. This source review does not replace those future successful receipts. Direct dependency pins are checked; recursively freezing every import and proving the binary importer correct are outside this bounded delta review. The planned family theorem still does not identify saved graph rows, establish endpoint/weight columns, close the reference refutation premises needed for actual snakes, or improve a numerical bound.

## Reviewed hashes

All paths are relative to `E:/Snake-in-a-box/milestones/92-full-witness-batch/`. Every revision hash matched the corresponding file in the final inspected manifest.

| File | SHA-256 |
|---|---|
| `scripts/build_closure.py` | `b9c239435bb8abb866fabf34f9505366e1432a6dee64268c2476fe08ec49b30d` |
| `scripts/check_batch.py` | `f4c2c33cf036db06cbdef868bd47350d514092ffeb66664889148daaaed78f24` |
| `data/checker-revisions.json` | `a942e2578582ca3355d8d06eca44120cf66e72798ad98b3b2ec77c63bb8c17da` |
| `data/repairs/check-batch-before-dispatch-pin.py.txt` | `95d7a4223a423cc7445c4c60739ab8662e1b51d478d072b5dd0bafa85393f54e` |
| `data/repairs/check-batch-reviewed-before-closure.py.txt` | `09490a4ded5026ca1bf64b105a48eaf22ab81d42c4a4402ee141313998c408b6` |
| `data/repairs/check-batch-before-memory-gate.py.txt` | `cddb288037918944ee4ffbe95c7f859ff40e88fd9e6666ffffff36239db3958a` |
| `data/repairs/check-batch-before-dependency-recheck.py.txt` | `d1947ff790c597f71452c7f9c1818264eff27c0b91b43a33a819ee39d2ca14d9` |
| `data/repairs/check-batch-before-lock-retention.py.txt` | `2fd6e388bd6f61dd01bb836884a6cdbe12a3a9bf4fbe014c3a6bfa33a5b68fac` |
| `data/repairs/check-batch-before-final-scope.py.txt` | `9db2b6acc18aa19bf33ef8be575f8235082848edf1de586b2ec249dca689dce9` |
