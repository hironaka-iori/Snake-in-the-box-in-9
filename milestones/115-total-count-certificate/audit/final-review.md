# Final bounded review of milestone115

No substantive mathematical overclaim was found in `mathematical-note.md`, `README.md`, or either handoff template. This review inspected their complete text and the preservation verifier's source. It performed only small metadata/hash comparisons; no Lean, solver, graph scan or large archive replay was run. Earlier independent review files and their pins were preserved.

The documents correctly distinguish the checked concrete interpretation of the selected $012310$ clauses, completed native export simulation, the running segmented Lean refutation, and its pending actual-snake composition. The plan records 1,396 exported modules, 287,753 deductions, 16,816,989 hints, 21,456 slots and successful native simulation. The final actual-snake module makes 1,397 planned modules. Generated modules and a checked initial group are not presented as a completed contradiction.

The 16 probe records comprise nine `UNSAT_UNCERTIFIED`, two `UNKNOWN`, and five `SAT_LOCAL_WITNESS` results. Every probe hash recorded in `probe-audit.json` and every positive-witness hash recorded in `witness-audit.json` matched the current file. The witness audit covers all five positive models. The strongest $012345$ candidate remains a lower total of 23, based on native rejection of total at most 22 after five validated cycle cuts. The recorded formula has 3,589 variables and 59,448 base clauses; the five cuts are added separately by the solver. The earlier short attempt remains inconclusive. The positive control $[6,3,6,2,6]$ is correctly described as a six-component local forest, with no complete-snake sharpness claim.

The finite means, potential ranges and integer comparisons agree with the previous independent graph reviews. The coefficient ceiling and the transfer from total22 to total23 correctly depend on the preserved cycles, nondecreasing surviving-edge weights and the existing all-edge potential certificate. The text preserves the distinction between a valid reused range and a minimum possible range. It reports no new global upper bound and leaves the maintained contributor interval distinct from a completed independent rebuild.

The archive record lists nine proof archives and 2,792 source members, consisting of two trees of 1,396 files. All 2,792 member paths and hashes were independently matched to `total-plan.json`. This check compared metadata; it did not decompress or rehash the large archive streams. The source of `verify_saved.py` verifies each proof archive's compressed identity, and in freeze/restore mode verifies the decoded identity. It checks source-part ordering and aggregate bytes, then requires each tar member's exact name, regular-file type, size and content hash, rejects unsafe paths and duplicate names, and rejects missing or extra members. Existing different target bytes are never replaced. Verification mode checks the frozen archive bytes; member decompression occurs during freeze or restoration. These distinctions match the README's restoration instructions.

The freeze logic excludes builds, archived originals, live logs, lock files and `batch-progress.json`. It admits generated-module receipts only when their module occurs in the fixed summary, and includes explicitly selected immutable evidence. This is suitable for a dated checkpoint while the batches continue. At this review's final inspection, `proof-summary.json`, `checkpoint.json`, `additional-evidence.json` and `file-manifest.json` had not yet been written. Consequently, final package freezing, the actual selected-evidence list and successful verifier execution are **outside this review's completed checks**. This is a pending finalization step, not a failure of the inspected mathematical evidence. The live batch state was read as status data; no independent process-liveness claim is made here.

No changes to active scripts, live proof artifacts, earlier audits or manuscript sources were made. The finalizer must include this report in the frozen manifest after creating and verifying the remaining package records.

## Reviewed pins

Paths are relative to `milestones/115-total-count-certificate`.

| File | SHA256 |
|---|---|
| `mathematical-note.md` | `628fbad21525ce6cc1c7eca872a978224db680fed5b9fe3476f9841bdf9bf11d` |
| `README.md` | `e90b4e43637072e5de3410ee6861cc994fee1db0fd1d4b80580cc2e15bd1fd58` |
| `handoff-templates/README.md` | `6ebc01f9e19d6c3cf85a9d83b0d9d7d38cdff1fdc27175164be60b19c6526a3f` |
| `handoff-templates/NEXT_AGENT_PROMPT.md` | `bbd6684420d4ff1d21f3bb5950b927f18f7fade33d568213597c2b7a58888be1` |
| `scripts/verify_saved.py` | `30dc1104f9dd6be9b3d2fde61335856e4bc7121858e96ac7826489661c9f5206` |
| `data/probe-audit.json` | `049d836eb547860ac3fa9cbf6881ab846ce7bd26d237e5db1ade94e972d8448b` |
| `data/witness-audit.json` | `406325336c13a5f7e15e781605a5ec1e901ac4e98aee97e92ddb48de494a6aa4` |
| `data/large-artifact-archives.json` | `2e15ed1b0e174e8e00c41c4794f14147147d363c7b0f0e5ac260a858f58879d6` |
| `data/total-plan.json` | `653a7c79821971a222777a93ebd73474ee4c53fbc2ffda084adf5c05c4527ee4` |
