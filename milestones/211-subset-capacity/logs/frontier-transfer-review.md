# Fixed frontier-transfer review

Date: 2026-11-14. Result: all inspected transfer equalities and hash pins agree. This review reads the frozen round-209 case and the fixed round-211 transfer artifacts only. It does not read the active round-211 `state.json`, inspect new jobs, or control any process. No test, compiler, Lean, solver, or search was run.

## Complete inherited-file comparison

The frozen round-209 `data/case-23` contains 606 files: 600 files in 100 historical run directories, plus the four model/input files, original initial state, and final state. Their relative paths and freshly recomputed hashes exactly equal the complete `source_files_sha256` map in `data/frontier-transfer.json`.

All 14,845,754 source bytes were independently compared with the corresponding round-211 inherited bytes. There were no mismatches. The two deliberately replaced state filenames were compared through their explicit copies:

- Old `state.json` equals new `source-state.json` byte for byte.
- Old `initial-state.json` equals new `source-initial-state.json` byte for byte.
- Each of the other 604 inherited files has the same relative name and exact bytes.

This includes the entire ordered 100-receipt prefix and all original input, output, before-state and after-state files. The historical native traversal was not re-executed or re-proved here.

## Exact transferred state

Starting from the frozen old state, independently replacing only `engine_pins` and adding `transfer_record = "data/frontier-transfer.json"` reconstructs the new fixed `initial-state.json` exactly, including its JSON serialization and SHA-256. No other field changes.

The seven saved region IDs, in their retained order, are 13, 12, 96, 106, 105, 104, 103. All seven complete 81-entry domain vectors are equal. No pending region is removed, added, reordered or weakened. The unchanged fields include:

| Field | Preserved value |
|---|---:|
| Version | 1 |
| Case | 23 |
| Status | OPEN |
| Committed jobs | 100 |
| Next region ID | 107 |
| Nodes | 2,683,356 |
| Recorded seconds | 245.65499999999994 |
| Historical receipts | 100 |

All four model pins are identical and agree with the source and destination files. All seven old engine pins agree with round 209; all seven new engine pins agree with round 211. Only the C source, continuation wrapper and executable have changed engine hashes. The model helper, resource helper, lower-dimensional input and square-capacity census are unchanged.

The old state hash agrees with both the transfer record and the case-23 entry in the pinned round-209 completion record. All recorded source counters and the reported seven-region count also agree.

## Transfer script and engine boundary

The script refuses an existing destination, checks the completed source state's pins, copies the historical case, verifies every copied file, preserves both old state files explicitly, and then creates the new initial state with the two changes above. Its proof gate refers to a saved successful `Subset211` receipt. The receipt reports PASS, exit code zero, and no stop reason; its source, object and 14 recorded dependency hashes were independently recomputed and agree. This is an integrity inspection of saved proof evidence, without a new compiler run.

The old and new C `visit` function bodies are exactly equal. The old and new Python `one_job` function bodies are also exactly equal. Consequently the explicit transfer preserves the old unfinished regions while changing only their subsequent propagation engine. The mathematical scope of that new propagation is reviewed separately in `logs/subset-engine-review.md`.

This establishes the fixed transfer's consistency. It supplies no acceptance of later receipt transitions, new exclusion, search completeness certificate, or complete snake-to-model interpretation. The active continuation remains outside this report.

## SHA-256 pins

Paths are relative to `E:/Snake-in-a-box/milestones/211-subset-capacity/`, except the explicitly marked round-209 entry.

| Artifact | SHA-256 |
|---|---|
| `scripts/transfer_frontier.py` | `f6f79e04121bc44e201c339aa970f49353fd4b624fdc430b47cb6c7934ba136e` |
| `data/frontier-transfer.json` | `f7cf9328de2e9838bcb8c727962aebad8ce0efd7ee4a037125f7782013ebef9c` |
| `data/case-23/initial-state.json` | `6d1487feec1c8ac398493d76a9ea491113d55f779cacb399fc9ad2822fcf5883` |
| `data/case-23/source-state.json` | `ec3701961111ed7af971295d4512853adaa4f26dc120bc559e70e39b4176d32e` |
| `data/case-23/source-initial-state.json` | `59682bca085516bfa92cb857fbce7fe2eb72239b766c3e721396ff4186961b28` |
| `data/Subset211-audit.json` | `3f471492d909e45637731ff62245b37bd86fe41e2e4c947e3831378f2a9fe1e7` |
| Round 209 `data/completion.json` | `6e67868dda6b250947ff1f3d181d5e96d89eb6d4031218aea5b4d7f4e3feaf80` |
| `data/case-23/model.json` | `f016ce4f452b404dd9b539218bddd7ae514e75bff5c901ab15a6a586b9df04d3` |
| `data/case-23/permutations.json` | `7e4e3dde90085bc5365ae29d2af69af62281fe52d69ea73482e4ef257a0abb93` |
| `data/case-23/input-tail.txt` | `c93b3f9b4cff719e4b471ed96422b3e245e16cbfdb4a43bf2ea150115d2fff1e` |
| `data/case-23/capacity-constraints.json` | `b0ff9653b522574b4e51219d355d6337a47039633f4c371333ef95376c72df91` |
| `scripts/capacity_solver.c` | `54aef14e94221646ffe5851a7e4ec0a6a43700bbc1f4f66c024f5dc51f6aeea4` |
| `scripts/capacity_continue.py` | `3a4456d34ce204769201c50c19cd35a2c71804698c449358e7f083a2dc992e46` |
| `build/capacity_solver.exe` | `08b74acdbbf7f8848dc44c774e4e58574e535f46eb4237089e7b7d23452b6ffb` |
