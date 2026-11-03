# Streaming transport and pilot source review

Status: `PASS_BOUNDED_TRANSPORT_AND_UNCHECKED_PILOT_SOURCE_AUDIT`.

No mismatch was found between the audited native count-free core, its variable/clause transport, the packed certificate, saved checkpoints and generated pilot. The new pilot remains unchecked by Lean in this review.

The accompanying JSON records all input/source pins and the complete 38-module pilot manifest. Its SHA256 is `e705a688230c84116ec26e25a6fad5f2ad0bab89e09f5f7a832adf14e3c97eec`.

## Independently recomputed

- Verified all 13,655 original core IDs and every compact input literal against the original count-free 92,640-clause CNF. The variable map is a bijection onto 1 through 5984, with all 5,442 active variables first. The original native proof SHA256 remains `4235b4df6ed6423a9148594572aa5f108b2106770c5dfc6b9b46cf0c9db0bf23`.
- Recomputed every reference count, last-use index, reusable-slot assignment, tree-key assignment and segment boundary. Every reference is read before its expiring slot can be overwritten. The 13,655 allocated slots fit within a height 14 tree with 16,383 keys.
- Compared every original deduction with both transported formats. All 58,182 clauses and 5,350,080 ordered references match the renamed LRAT, packed words and packed-index rows. Literal signs, order and multiplicity are preserved. Original retained input IDs map to their compact ordinals; derived IDs remain unchanged in the renamed LRAT.
- Independently reconstructed all 28 saved live checkpoints from slot ownership and clause entries. Every checkpoint's 16,383 entries, live-clause count, ordering and hash matched. This reconstruction did not perform propagation.
- Verified all 38 generated source hashes and their import order. The base and fast helper sources equal the pinned 144 versions under the explicit 150 namespace/import substitutions; the fast checker retains 14-bit masks and shifts. External project imports are exactly `LocalWindowModel` and `LocalWindowCnf.ShareWindow150`.
- Parsed the current concrete CNF into 107 raw chunks, comprising 106 chunks of 128 clauses and a final 87-clause chunk. Checked all 107 subtree clause lists and slice references, and all 13,655 initial raw clauses under their expected preorder keys. The chunk-truth source includes every chunk exactly once.
- Compared the generated pilot proof and checkpoint literals with the corresponding packed stream and saved checkpoint.

The literal offset remains 8192. The maximum possible encoded literal word under the semantic variable map is 14177, below the 14-bit limit 16384. The recorded maximum clause length 81 and maximum reference count 860 fit the existing 255-literal and 4095-reference fuel limits.

## Exact scope of the pilot

The pilot contains the first 2,169 deductions and 6,151 references. Its checkpoint has 13,466 live clauses. Its proposed `prefix_true` theorem assumes truth of the exact input CNF and concludes `TreeTrue` for the checkpoint after that prefix. The generated check includes both successful prefix replay and `cpOk` against the saved checkpoint. It does not assert a final contradiction.

The complete transported certificate ends with original empty clause 205425 at tree key 12069. Its 878 segments would require 28 groups and 27 full group-boundary checkpoints. The generator's expected 342-module full inventory is arithmetically consistent, but this review checks the 38 emitted pilot sources; it does not claim that a full Lean replay has been generated or completed.

## Inspected evidence and remaining obligations

The complete native and packed RUP receipts were inspected and their source/artifact pins checked. Their propagation implementations were read; unit propagation was not repeated. The independent recomputation here covers transport, allocation, checkpoint contents and emitted source data. It took 7.375 seconds.

The fresh 150 helper modules, initial-tree truth bridge and pilot check/consequence still require compilation. Completion then requires all 878 segment checks, checkpoint transitions, group compositions and the final empty-clause theorem, followed by the separate semantic and actual-snake assemblies. The unchanged inherited helper proof text does not by itself establish that its new module instance has compiled.

This review verifies the exact literal bijection and concrete CNF. It does not replace the separate clause-semantic checks for the meanings of all 5,984 variables. No Lean, solver, Git or process-control operation was performed. The active 147 and 150 processes were untouched, and only the two transport-review files were written.
