# Milestone 152: completion source review

The bounded source review found no blocking acceptance or mathematical-premise defect. This is a source and saved-evidence review. The complete replay and the final actual-snake composition remained pending at the recorded observation: 137 of 342 modules accepted, with `ReplayCheckpoint150_00320` active. Neither `data/replay-completion.json` nor `data/ShareComplete152-audit.json` existed.

## Acceptance requirements

`audit_full.py` refuses incomplete replay with exit code 2. On completion it requires the exact 342-module execution order, no active module or batch lock, matching plan/driver/checker hashes, and every accepted receipt. For every module it verifies the current source, object, compiler log, source/checker snapshots, explicit dependencies, source-plan hash, successful compiler status, and expected number of axiom reports. The total must be 1,027 reports, using only `propext`, `Classical.choice`, and `Quot.sound`.

The final receipt must report `Snake9.ReplayFull150.unsat`. The pinned native transport must contain all 58,182 deductions and 5,350,080 references, with final original empty-clause ID 205425 and tree key 12069. Its artifacts and checkpoints are rehashed. The existing independent milestone-151 source-layout review and its source pins are also required. The closed contradiction source composes all 28 groups, ending with group 27, rather than accepting the initial prefix or a checkpoint consequence.

`check_complete.py` requires completed replay and the separate successful audit record before it invokes Lean. It checks the audit's plan and final-refutation receipt hashes, then checks the final source and imported receipt/source/object/dependency closure. It publishes acceptance only after a successful compiler result and the standard axiom check. The recorded guard tests rejected incomplete states at 124 and 125 accepted modules, respectively; those are producer-run guard tests, not tests rerun by this reviewer.

The completion plan was independently reconstructed from the milestone-150 semantic plan. All seven checker transformations were reproduced as string operations and matched the saved checker exactly. Preparation source pins match current files.

## Actual-snake statement

The proposed theorem is `Snake9.ShareTransfer152.share16`. For a snake `p : Snake m`, a valid six-transition window starting at `r`, and either orientation having canonical direction word `012032`, its conclusion is

\[
16\leq\sum_{i=0}^{4}\operatorname{coreShare}_{12}(p,r+i+1).
\]

The source passes `Snake9.ReplayFull150.unsat` to the already checked conditional implication `share16_of_core_unsat`. There is no remaining pair-count, parity, endpoint-location, or additional share-floor premise. The adapter supplies the ordinary five broad bounds from the snake itself and handles reversed canonical words through path reversal. The source uses the five internal centres, at positions `r+1` through `r+5`.

The milestone-150 conditional implication and semantic-assembly receipts, sources, objects, and logs were hash-checked. Their entire transitive closure was not independently re-audited here. The new milestone-152 theorem is still unchecked until the required full contradiction and final compilation succeed. It makes no global upper-bound claim.

## Final serialization

The continuation waits for the original serialization record to report `RESUMED`, successful transfer, and successful resume, together with the completed 342-module replay. It then runs the complete audit before the final serializer, checking pinned script hashes before each stage.

The final serializer independently requires those completed records. It identifies and retains the same milestone-147 coordinator process, waits for its outstanding checker and all Lean work to finish, and launches only the final composition checker. Its normal cleanup and recovery watchdog both wait for the owned final checker, including its preflight, as well as outstanding Lean processes, before resuming the held coordinator. This was inspected in source only; abnormal termination and watchdog recovery were not exercised.

## Share-17 strengthening query

The separate preparation asks whether canonical `012032` windows have share at least 17 by imposing cap 16 at resolution 12. All five count bounds are `[0,21]`, the radius is four, and the ordinary endpoint budget is two. The saved input has 11,651 variables and 94,331 clauses, with no appended pair condition or extra cycle cuts. The input hash, header, clause count, meanings length, producer pins, and generated-driver transformations match their records. This review did not independently rebuild every clause.

The saved native status is `TIMEOUT`: a 60-second limit, 62.563 seconds recorded elapsed time, and 66,801,664 bytes of partial proof output. The driver did not enter successful native replay. No contradiction, share-17 theorem, or sharpness of share 16 follows from this attempt.

## Frozen evidence and limits

The accompanying JSON contains exact source, receipt, object, log, query, and preparation hashes. It also records the time-specific running-state snapshot separately from fixed source pins. No compiler, solver, proof replay, process-control action, or Git operation was executed during this review. Only the two assigned audit files were written.

The JSON SHA-256 is `2f5b106b50a811dab02c0df9f72f3c4b4b5c7cd7ac798f3df21155fd174f0c65`.
