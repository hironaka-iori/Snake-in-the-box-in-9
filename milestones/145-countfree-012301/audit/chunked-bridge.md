# Chunked initial-database truth bridge

Status: `PARTIAL_ALL104_PART_TRUTH_CHECKED_FINAL_ASSEMBLY_TIMEOUT`.

All 104 part-level truth-transfer theorems passed Lean. The final assembly did not complete within its 180-second limit. No theorem establishing truth of the entire preserved initial database is available from this task. The stopped prototype, both unsuccessful equality assemblies, both small proof-script errors, and the final timeout are preserved with exact source and checker snapshots.

## Checked results

The data-only module `ChunkData145` passed in 83.234 seconds. Its maximum sampled private memory was 1,349,042,176 bytes. It contains the 104 small input-tree definitions and the original combined tree, without attempting the large equality proofs.

Thirteen `ChunkParts145` modules checked all 104 part-clause equalities and all 104 equalities identifying each built part with the corresponding preserved `LiteralData144.part`. The clause-list equalities require no axioms. The build equalities use only `propext`.

`ChunkTruthTools145` checked three generic lemmas: truth survives taking a slice, truth passes to a sublist specified by membership, and an input-tree part is true when its clause list is such a true slice. Thirteen `ChunkTruthPartsFixed145` modules then checked:

- 104 exact equalities locating each part's clause list in at most two adjacent original CNF chunks.
- 104 implications from truth of those original chunks to `TreeTrue` of the corresponding preserved literal-tree part.

The slice equalities require no axioms. The generic truth lemmas and part-level truth theorems use only `propext` and `Quot.sound`. In total, 28 modules passed with 419 checked axiom reports. Source, object, compiler-log, checker-snapshot and dependency hashes were rechecked when the completion receipt was written.

These are facts about the preserved milestone144 database with 13,224 input clauses. They do not establish the selected milestone145 share-16 theorem or complete any LRAT replay.

## Pending final statement

The attempted assembly is in namespace `Snake9.ChunkData145`:

```lean
theorem start_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ
      Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.start
```

Its source is `lean/ChunkTruthAssemblyFixed145.lean`, SHA-256 `08abee629d93337b5cc1c6214d4beacdc683ebbdbeda7fa04acfe8664e4ba38b`.

The proof candidate first obtains truth of each original raw CNF chunk, uses the checked part-level implications, and combines those parts with the remaining node clauses by `TreeTrue` constructors. It avoids the full-tree clause-list and materialization equality theorems.

The check stopped at 181.610 seconds with `TIMEOUT`. Maximum sampled private memory was 1,248,415,744 bytes. The compiler log is empty, and there is no axiom report or accepted object for this assembly. These observations establish neither success nor the exact stage consuming the time. A prefix-truth theorem depending on this statement must remain pending.

## Preserved attempts

| Module | Result | Seconds | Maximum sampled private bytes |
|---|---|---:|---:|
| Original `InputData145` prototype | Memory limit |74.562|3762462720|
| `ChunkAssembly145` | Memory limit |62.015|3635290112|
| `ChunkAssemblyRepair145` | Memory limit |44.984|3420532736|
| `ChunkTruthParts14500` | Invalid Boolean theorem projection |2.735|No owned sample before exit|
| First `ChunkTruthPartsFixed14500` | Residual Boolean equality unclosed |2.765|No owned sample before exit|
| `ChunkTruthAssemblyFixed145` | Timeout |181.610|1248415744|

The small Boolean proof errors were corrected by rewriting the two truth hypotheses and closing the resulting equality by `rfl`. The failed source bytes remain in the compiler snapshots and repair receipts. Their automatic error-placeholder axiom reports were rejected; only the later passing receipts are counted above.

The equality repair used one simplification pass instead of 104 sequential rewrites. It still stopped before the first immediately placed theorem report. This places the failure at the initial full-tree clause-split equality or an earlier loading/elaboration stage; it does not identify a more precise kernel operation. The direct truth-transfer method stayed below that memory usage during its bounded attempt, but did not finish. No general performance claim follows.

## Evidence and continuation boundary

`data/chunked-bridge-completion.json` contains all successful module receipts, the six preserved unsuccessful runs, the full current source map, dependency hashes, exact pending theorem, and resource observations. Its SHA-256 is `636ce08141dfce6b1824c3274f84979fed223830115f20191ab39a1deae75c7e`.

The original generator is `scripts/prepare_chunked_bridge.py`. The first repair transformation is recorded in `data/chunked-bridge-repair1.json`. The complete source of the second repair generator is stored in `data/chunked-bridge-repair2.json`; the subsequent Boolean corrections are separately recorded in `data/chunked-bridge-repair2-boolean-fix.json` and `data/chunked-bridge-repair2-rfl-fix.json`. Existing sources and receipts were not replaced with a success status.

No further compilation or repair is part of this task. If another attempt is authorized, the most direct diagnostic split is to check original-CNF-to-individual-chunk truth separately from the final constructor assembly. The current empty final log does not distinguish those costs. The preserved prototype and all milestone144 source files remain unchanged.
