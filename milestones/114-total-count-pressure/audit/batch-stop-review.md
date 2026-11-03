# Milestone 104 stopped-batch review

Read-only inspection, 3 November 2026. No compiler, solver, batch restart, or source modification was performed. The only saved output is this report.

## Finding

The authoritative batch state is `STOPPED`, with no active module. The final attempt was `ConditionalBatch104G080`; it ended after 55.594 seconds with exit code `1073807364` (`0x40010004`), `timeout: false`, and an empty compiler log. The wrapper's exception text says “Lean error; inspect the preserved log before resuming”, but that text is generated for every nonzero, non-timeout exit. It is not a Lean elaboration diagnostic.

Microsoft's source identifies `0x40010004` as `DBG_TERMINATE_PROCESS`; the Microsoft error-code reference describes this status as process termination by a debugger. This supports classifying the saved event as abnormal process termination. It does not identify who initiated it, and the local evidence does not establish a user pause. See [Microsoft's constant declaration](https://github.com/microsoft/ptvsd/blob/master/src/ptvsd/_vendored/pydevd/pydevd_attach_to_process/winappdbg/win32/kernel32.py#L2831) and [MS-ERREF](https://winprotocoldoc.z19.web.core.windows.net/MS-ERREF/%5BMS-ERREF%5D.pdf).

No successful receipt or object exists for the failed conditional group. Its preserved source snapshot equals the current source and the attempt's recorded source hash. There is therefore no checked proof from this attempt to reuse, and no recorded proof error that justifies changing its mathematics or tactic.

## Preserved progress and bounded verification

The stopped state records 153 successful groups, covering 97 completed-profile contexts and 94 conditional-profile contexts. It leaves 1,004 groups, or 694 completed and 697 conditional contexts. Complete graph-potential certification remains false. The batch stopped at 2026-11-02 23:12:54 UTC.

I verified source, source-snapshot, object and log hashes for the last three successful receipts: `ConditionalBatch104G079` (30.25 seconds, four audits), `CompletedBatch104G080` (73.766 seconds, three audits), and `CompletedBatch104G081` (133.016 seconds, three audits). This review does not independently revalidate all 153 receipts; the existing resumption driver performs that validation before reuse.

The saved plan, checker and generator hashes still match the stopped-state pins. No milestone104 Python/Lean process or lock file was found during inspection. This is a process snapshot, not a guarantee about a later launch.

The next unchecked group is conditional group 80, with contexts $(70,0)$ and $(73,0)$, acceptance root 2715, potential nodes `n5_75` and `n5_64`, slope 496 and range 602. Its joint-traversal source expects four printed theorem audits. The baseline alternative is separately listed in the plan; the current driver selects that alternative only after a timeout. The saved event was not a timeout.

## Safe next action

The smallest justified continuation is one explicitly initiated, monitored retry of the unchanged `ConditionalBatch104G080` through the existing single-module checker, after confirming the process/lock state and pins again. No source repair is indicated by the saved evidence. This retry preserves the earlier failed attempt under its unique log/snapshot identifier and cannot replace it with a successful receipt silently.

If that module passes, the existing batch driver can reuse its receipt and the previously successful groups after hash validation. A bounded driver run with `--max-groups 1` also reuses cached groups and permits only one newly compiled successful group. The audit did not start either route. If the termination corresponded to an intentional pause, unchanged resumption is safe under these guards; the cause must not be recorded as a user pause without additional evidence.

A repeated termination code should first be investigated as a process/runtime interruption. A future concrete Lean diagnostic would supply the basis for a source repair. The present empty log supplies none. Switching proof implementations merely because the wrapper used the phrase “Lean error” is unsupported.

## Evidence hashes

Paths below are relative to `milestones/104-complete-potential-batch`.

| File | SHA-256 |
|---|---|
| `data/batch-progress.json` | `157682ee6cfbf8ec8f08fa05e5b05c3fc3ade9f3677d59b32012bce0ed678457` |
| `logs/ConditionalBatch104G080-1793661117967943200-record.json` | `4c9bcd784ee0f348adf861f6a74a73ebe3cc57fe35cc0bf0d7f01a06a7ee7622` |
| `logs/ConditionalBatch104G080-1793661117967943200.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `logs/check-run-1793661117967943200.json` | `50ac13c70be3afac6b6ce74796925d09db16a06f16ac87c8deea0e7ae196f124` |
| `logs/batch-1793649486435169100.log` | `57f3c82a6503a1c223e0e1a25485c0703ffa0f15dc0583284880fe7ccc73b9cf` |
| `lean/ConditionalBatch104G080.lean` | `e81d6b62b268ceb1aeec5cead44dc2a9c593f787e72eacba6e8dc7cbecabbbff` |
| `scripts/run_batch.py` | `a5fd5b3f015a35ac203c0a0b532436d4fd5ca833ad52f76ea4e287a91639de72` |
| `scripts/check.py` | `7c30d216e241c795fb24788e424e8faca86f64922a18ec84b4bee8fb5e385261` |

The failed attempt's source snapshot is `logs/attempt-1793661117967943200/ConditionalBatch104G080.lean.txt`, with the same source hash shown above. The authoritative stopped-state exception, wrapper assertion, exit record and zero-byte log are mutually consistent with termination before any saved compiler diagnostic. They do not establish whether the unchanged proof would pass.
