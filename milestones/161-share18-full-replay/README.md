# Accepted pilot update

The first32 continuation segments passed Lean. Read PILOT_COMPLETION.md and data/pilot-completion.json. The full replay remains pending. The preparation description below is historical.

# Milestone161: remaining share18 replay

Status: transport and source-generation scripts are prepared. No transport, export, native resource snapshot, compiler or solver was run during preparation. Root-owned kernel checking scripts are separate from this package's preparation scripts.

The target is the remaining144,160 deductions and14,704,875 references of the existing144 proof. The initial state is the checked `Snake9.Checkpoint160.afterPrefix`, whose truth follows from the original compact CNF. The accepted1,055-deduction prefix and its6,006 references are reused without recompiling160.

## Preservation and scope

The transport preserves the compact input IDs, existing variable renaming,14-bit physical keys, depth14 tree and offset8,192. It checks the compact core against its original clause IDs and map, reproduces the exact160 allocation digest, compares every accepted prefix packed integer, and reproduces160's live-entry checkpoint. Every remaining packed row is decoded back to its exact destination, literal words and hint keys. Hint ownership is checked before expiring clauses are overwritten.

The full remaining proof is not replayed for native unit propagation in this stage. The receipt states `full_remaining_unit_propagation_replayed=false`. The original144 independent native certificate remains prior evidence; the new Lean replay must check the transported proof's validity. Passing transport alone is not a proof of the contradiction.

The remaining proof is split into2,415 segments of approximately6,000 references,76 groups of at most32 segments and75 materialized checkpoints. Packed proof rows are streamed to a length-prefixed binary file; checkpoint entries are compressed JSON. Checkpoints keep live entries and replace dead entries with tautologies, as permitted by `cpOk`.

## Source output and pilot

The emitter makes two deterministic passes. The first measures and hashes every complete source without writing a Lean file. The128MiB source cap is checked against this exact UTF-8 total. The second pass must reproduce each measured size and hash. An oversized result stops after saving its measurement; it does not write the source package.

The expected output is833 modules in `lean/`, with a complete topological order and source hashes in `data/full-source-plan.json`. The plan contains all artifacts, the12-module pilot subset, segment/group coverage, transport receipt path/hash, external receipts, final theorem type and exact source size. `ReplayPilot161` belongs to the complete module order as well as the pilot subset.

The pilot comprises the checkpoint after32 remaining segments, their data module, eight check modules, the group consequence and `ReplayPilot161`. Its theorem derives truth of that checkpoint from the original CNF using the accepted160 theorem. Full kernel replay must wait for acceptance of this first group. The final assembly target is `Snake9.ReplayFull161.unsat : Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow144.cnf`.

## Resource gates and future invocation

The native preparation runner permits one worker, requires1.5GiB free memory before launch, reserves768MiB during execution, monitors combined parent/worker private memory against1GiB, and stops after600seconds. It refuses overlapping Lean, recognized graph or159/160 batch work. Native Windows queries are used without CIM. JSON reads, writes and atomic replacement have bounded `PermissionError` retries. The private-memory threshold is sampled every0.2seconds; it is not an operating-system allocation cap.

From `E:\Snake-in-a-box`, the future native preparation command is:

```powershell
& 'C:\Users\hironakaiori\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' -B -X utf8 'milestones/161-share18-full-replay/scripts/run_prepare.py' --label remaining-v1
```

This command has not been run by the preparation task. It will save `data/remaining-v1/transport.json`, the exact source-size measurement, binary proof, compressed checkpoints, process logs and final source plan. Kernel execution is a separate root-owned step with its own acceptance gates. Existing source plans and run folders are never overwritten.

`scripts/prepare_sources.py` performs only source syntax and pinned-file checks. The existing144–160 files remain unchanged. The local share18 theorem and all global consequences remain incomplete until full contradiction replay, actual-snake composition and reversal pass.
