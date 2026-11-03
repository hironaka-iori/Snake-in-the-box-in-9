# Completed pilot and full replay source review

Status: `PASS_COMPLETED_PILOT_EVIDENCE_AND_FULL_SOURCE_LAYOUT_AUDIT`.

The completed pilot evidence matches the saved source, object and log bytes. The full generated source contains every segment and checkpoint transition and composes all 28 groups into the intended final CNF contradiction. No indexing, omitted-segment or final-empty mismatch was found. Complete Lean replay remains a separate requirement.

The accompanying JSON records exact source pins, all 38 pilot receipts and the review's limits. Its SHA256 is `ed6039bfdfca718e46384b58cff5eee6542010c3dbfee53311bef30c54aab601`.

## Completed pilot

Revalidated all 38 successful pilot receipts, their source/object/log hashes and 1,279 explicit dependency-hash references. Parsed all 120 axiom reports directly from the pinned logs and compared them with the receipts. Only `propext`, `Classical.choice` and `Quot.sound` occur. All pilot sources remain byte-identical to the audited milestone150 sources.

The three central conclusions are:

- `Snake9.ReplayData150.start_true`: truth of the exact CNF implies truth of the complete materialized initial database containing 13,655 clauses from 107 raw chunks.
- `Snake9.ReplayPilot150.prefix_check`: the first 2,169 deductions and 6,151 references pass the closed checker, and the resulting database satisfies the saved checkpoint check.
- `Snake9.ReplayPilot150.prefix_true`: for any Boolean assignment, truth of the CNF implies truth of that post-prefix checkpoint.

These are verified existing compilation results. The pilot does not establish unsatisfiability of the full CNF.

## Full generated source

Rehashed all 342 generated modules, totaling 36,831,638 bytes. Both source and execution orders satisfy every project import. The external project imports are exactly `LocalWindowModel` and `LocalWindowCnf.ShareWindow150`. No proof placeholder, added axiom or `native_decide` occurs in the generated sources.

The generator's `initial`, `pilot`, `full` and common emission functions have identical syntax trees to the audited 150 generator. Changes route input to 150 and output to 151, require `--full`, and require the successful pilot receipt. The generated theorem bodies are unchanged by those routing changes.

Compared every emitted proof literal with the saved 150 packed bytes, confirming all 58,182 deductions occur in order across 878 contiguous segments. Their recorded reference counts total 5,350,080. Checked all 27 full checkpoint lists and the pilot checkpoint against the pinned 150 data.

The source has exactly 850 ordinary `replay_true` transitions, 27 `cp_true` transitions and one `final_false` application. The last group covers segments 864 through 877. Its final check requires an empty clause at key 12069, corresponding to original clause ID 205425. The last packed deduction independently has that destination and an empty literal section.

`ReplayUnsat150.lean` imports and applies groups 0 through 27 without omission. Its stated conclusion is:

```lean
Snake9.ReplayFull150.unsat :
  Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow150.cnf
```

The temporary CNF-truth premise is discharged with `unsat_of_raw` after the final group's contradiction. This is a source-layout result; the full theorem is not certified by this review.

## First group and remaining limits

The first group's source covers segments 0 through 31: 3,728 deductions and 195,386 references. Its conclusion is `TreeTrue τ start32` from `TreeTrue τ start0`. It ends at a checkpoint and asserts no final contradiction. The active first-group run was neither awaited nor independently certified here.

The earlier 150 transport audit was reused after verifying its report and pinned inputs. This review did not repeat propagation, slot allocation, clause semantics or compiler execution. All later segment checks, group compositions and the final theorem must pass before claiming the complete contradiction. Actual-snake interpretation and any numerical upper bound remain separate assemblies.

One minor metadata issue remains: `full-source-plan.json` retains the inherited `emit_lean.py` regeneration command. The saved 151 generator is `scripts/emit_full.py`, used with `--full`. The emitted source and recorded generator hash are consistent.

The automated comparisons took 4.203 seconds. No compiler, solver, Git or process-control operation was performed. Only these two review files were written.
