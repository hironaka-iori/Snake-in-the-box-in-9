# Continuation transport requirements

Status: bounded source and metadata review; no continuation execution or compilation performed. The proposed continuation is compatible with the accepted checker provided the checks below pass. The 128 MiB source budget is plausible. A 1 GiB compiler budget is unestablished.

## Accepted starting point

Milestone 160 `data/completion.json` records `PASS_ACCEPTED_PREFIX_CHECKPOINT_TRUTH`: 1,055 deductions and 6,006 references have a checked checkpoint and a theorem deriving its truth from the original `ShareWindow144.cnf`. The native receipt retains its earlier source-only status; it must be combined with this completion and the three module receipts. The continuation starts with `Snake9.Checkpoint160.afterPrefix` and inherits truth through `Snake9.Checkpoint160.afterPrefix_true`.

The checkpoint contains 16,383 preorder entries, including 13,197 retained live clauses, in a height-14 tree. Its compressed JSON is 56,405 bytes; its Lean data module is 350,185 bytes. The 14-bit packing, offset 8,192, 14,114 allocator slots and physical-key permutation are part of the starting state. There are 5,779 active compact variables within the 6,371-variable semantic numbering. The compact input is already renamed; a second renaming is invalid.

The checkpoint relation is weakening. `LratFast144.cpOk R t` permits each clause of `t` to be a tautology or the same clause at the same key in `R`. It does not prove that every clause needed later survives. That additional transport condition must be checked against the saved proof and its allocation metadata.

## Exact continuation checks

1. Verify the accepted completion, module receipts, source and object pins, the checkpoint gzip hash, the saved compact CNF/LRAT pins and the original-input-to-core identity mapping before using the checkpoint. Preserve original clause identifiers and the existing variable map. Compare all 13,224 compact input clauses with their corresponding original clauses as in 160, or reuse a pinned receipt that establishes this comparison for the identical bytes.
2. Reproduce allocation over the whole saved proof, including the prefix. The allocator assigns initial slots by descending reference count with clause-id tie breaking, reads hint slots before expiring final-use clauses, uses the minimum free slot, and retains the final empty-clause identifier. Reproduce the complete allocation digest `eb67770943b4675559c9911383c12ff1a57f335021179aa222b284b4c33d7155`. Do not restart slot assignment at deduction 1,056 or free a clause after its first use.
3. Reproduce all 1,055 accepted packed prefix values, or compare an independently reproduced packed-prefix digest `cc7c70bbd6c00b515cb055093f0d23fefac448c23f0956d95a461b71cb8c02a8`. Reconstruct the owner of each live slot after the prefix. Decode the accepted checkpoint independently and verify its retained masks against those owners. At the cut immediately before zero-based row 1,055, a retained owner must have last use at least 1,055. Expiration at row 1,054 is already past; expiration at row 1,055 occurs only after its hints are read.
4. For every continuation hint, verify both its original clause identifier and current slot owner before translating it to a physical key. Check that its mask is present in the actual weakened database used for replay. This must also hold across every later checkpoint. A native replay against an unweakened side database alone cannot establish this condition.
5. Preserve the original core-to-preorder key permutation. Slots, clause identifiers and physical tree keys are different quantities. Check key injectivity, range 1 through 16,383 and complete 16,383-entry preorder checkpoint lists. A successful `cpOk` on a truncated tree alone would not establish complete continuation readiness.
6. Validate each packed deduction by independent decoding: destination, ordered literal occurrences, literal terminator, ordered hint keys and final terminator. Literal words are bit positions plus one, with negative literals offset by 8,192. Require all words below 16,384, fewer than 255 literal occurrences and at most 4,095 hints; the saved proof has maximum 710 hints. Ensure the parser consumes exactly the intended fields and no unexpected trailing data. Binary length records must have complete four-byte headers, complete bodies and exact end of stream.
7. Require an exact split after 1,055 deductions and 6,006 hints. The remaining totals are 144,160 deductions and 14,704,875 hints; full totals are 145,215 and 14,710,881. Hash the emitted packed continuation and record step/segment offsets, counts and checkpoint hashes. Do not count replaying the accepted prefix as new certified deductions.
8. Distinguish exact transport from validity checking. Remaining native RUP can be omitted if the export is explicitly transport-only and every segment is subsequently checked by Lean against its actual weakened starting tree. If native RUP is included, it must use that same weakened state and retain the clause-id/slot-owner assertions. The strict unit-or-conflict treatment in 160 is sufficient when it succeeds; Lean can skip non-unit hints. A strict native failure therefore needs interpretation before being called a proof failure.

## Modular Lean continuation

The saved `proof-plan-base.json` has 2,416 segments. Its first hint count is 6,006; the remaining 2,415 counts sum to 14,704,875. The maximum segment count is 6,471 and the final segment count is 987. Keeping these boundaries and grouping the continuation from its new segment zero gives 76 groups, 75 intermediate checkpoints and a final group of 15 segments. A regrouped stream must verify these boundary counts, rather than assume them from the approximately 6,000-reference target.

Reuse `LratFast144` and its existing `Tree` type directly. A renamed copy of the checker can create incompatible types and would require an additional bridge. Adapt the accepted 155 emitter structure:

- Each group data module imports its starting checkpoint and, except for the last group, the next checkpoint. Within a group, later starts are defined by replaying the preceding segment.
- Check modules contain at most four segment checks. Ordinary checks establish `check start proof = true`. At a group end, check `andB (check start proof) (cpOk (replay start proof) nextCheckpoint) = true`.
- Group consequence modules chain `replay_true` and use `cp_true` at the boundary. Their input is `TreeTrue` for the group's starting tree.
- The final segment checks `andB (check start proof) (hasEmpty (replay start proof) finalKey) = true`; the final group uses `final_false`. Keep the final empty clause in the replay tree. Checkpoint entry zero means a tautology, so writing an empty clause as an ordinary checkpoint zero would destroy this final bridge.
- A final composition imports the accepted 160 consequence, derives the first group's truth from the exact original CNF, chains all group consequences and obtains `Unsat ShareWindow144.cnf`. Record the final original clause id, slot and physical key independently. A clause-id value is not a valid substitute for its key.

The full CNF contradiction and the actual-snake theorem remain separate completion steps. The latter must use the accepted 159 semantic interpretation and the applicable actual-snake/reversal wrappers. Native RUP success and source generation do not replace these Lean checks.

## Source and memory budget

The saved compact LRAT is 105,893,029 bytes, with 145,215 deductions, 14,710,881 hints and 2,561,006 derived literal occurrences. The 14-bit format uses, before dropping high zero words,

\[
2{,}561{,}006+14{,}710{,}881+3(145{,}215)=17{,}707{,}532
\]

words for the complete proof. This gives a conservative raw binary payload bound of 30,988,181 bytes; allowing per-row rounding and four-byte lengths gives less than 31,714,256 bytes. The raw hexadecimal bound is approximately 61,976,362 characters. With per-row rounding and the 155 `nat_lit` list framing, the complete proof literal text fits below 64,000,000 bytes; the continuation is smaller. These estimates exclude declarations, checkpoints and other modules, and are derived from accepted metadata without parsing the proof.

Seventy-five checkpoints at the first checkpoint's 350,185-byte source size would add 26,263,875 bytes. That is an illustrative estimate, not a bound on later checkpoints. A 128 MiB total source cap leaves roughly 70 MB after the conservative full proof-literal allowance, before module overhead. The generator must measure each checkpoint and cumulative UTF-8 source bytes, stopping before the cap. The old 144 plan records 326,828,007 Lean source bytes with 603 checkpoints; copying that export cannot meet 128 MiB. Grouping by 32 is essential to the proposed reduction, but does not itself certify the cap.

For bounded native preparation, stream proof rows and binary packed records, retain only allocation metadata and the current database, and emit one group at a time. The masks for approximately 14,114 slots alone occupy roughly 24 MiB of bit payload at the existing literal offset. Dictionaries, integers, free heaps, expiry lists and Python allocation overhead add substantially to this. Avoid keeping all 14.7 million hint integers, every decoded proof row, every checkpoint and all generated source strings concurrently. The 155 emitter's global `files` dictionary and end-only source-size check should not be copied unchanged if predictable peak memory is required. Count bytes during generation, including temporary simultaneous string/byte encodings.

A 1 GiB private-memory limit is plausible for this streaming native export, subject to a measured receipt. It is not established for compilation: 155's accepted full replay completion records maximum sampled private memory of 2,036,826,112 bytes, approximately 1.90 GiB. The parent has confirmed separate intended limits: 1 GiB for native preparation and 3 GiB for the compiler, with a 2 GiB free-memory compiler startup gate. This distinction resolves the potential budget mismatch; it does not predict the new compiler peak. Source size is not a compiler-memory bound. Resource checks should distinguish native export from Lean compilation, use the accepted native monitor, and record peak private memory, sampling interval and termination conditions. A sampled monitor must not be described as an operating-system hard allocation cap.

## Minimal pilot acceptance

An optional early diagnostic is one exact continuation segment starting from the accepted 160 checkpoint, with complete ownership checks, a generated next checkpoint, a Lean combined check and a consequence theorem from the original CNF. Pin its exact start/end deduction identifiers and counts. This establishes that the cut and weakening are usable. A complete first-group pilot can subsume this diagnostic; no separate single-segment export is required.

Before approving the full group-32 execution, accept one complete 32-segment group and its checkpoint boundary under the intended resource limits. This pilot tests the actual replay-chain depth, import structure and checkpoint transfer. Require zero compiler errors, fresh expected objects, accepted axiom reports, matching source/object/dependency hashes, cumulative source accounting and resource receipts. One short segment alone does not establish group-32 compiler viability or later checkpoint sizes. Full completion still requires every continuation segment and the final empty-clause bridge.

## Additional review of the prepared 161 transport

The source `scripts/transport_remaining.py`, SHA-256 `95a27e8852bcbdc31a4850bb2387cf5c3c4857992903a3cee011dc719b4c96fb`, was inspected after it became available. No blocking owner, entry or checkpoint defect was found in this source review. It reconstructs the global allocation digest, reproduces every accepted prefix value and the exact accepted checkpoint, verifies all hint owners and their nonzero retained entries before expiration/overwrite, and maintains entries by exact insertion or checkpoint weakening. This invariant establishes the retained entries' correspondence to their owners; a separate per-hint clause-mask comparison is redundant under these updates.

Each checkpoint filters owners using last use at least the next absolute row, rejects a live zero entry, records 16,383 entries and installs that weakened state before continuing. The final empty clause is tested only after the last row, and no checkpoint follows it. Packing omits the final high zero hint terminator, which has the same natural-number value as the accepted encoding; remaining zero bits supply the terminator. Round-trip comparison verifies all explicitly stored words. The source's transport-only status and explicit absence of remaining native RUP are appropriate.

The accompanying `emit_lean.py`, SHA-256 `4dc6468d6ea97a2de4d90b0b847f612b8f9f3000871224efa504ace1e5f82734`, was also read for its group/checkpoint/final bridge and streaming strategy. It reuses the accepted checker types, emits the 32-segment consequence from `afterPrefix_true`, keeps final `hasEmpty`/`final_false`, measures all generated UTF-8 sources before writing, and regenerates them against measured hashes one module at a time. This avoids the old all-source dictionary. Its proposed twelve-module first-group pilot subsumes the optional shorter diagnostic. This review does not cover the native guard, complete dependency closure, compiler runner or execution receipts, and does not certify the generated sources before execution.

## Examined input pins

Paths below are relative to `E:/Snake-in-a-box`. Hashes were checked on the small listed sources and receipts during this review. The LRAT hash is inherited from accepted metadata; the LRAT was not reread or parsed in this review.

| Path | SHA-256 |
|---|---|
| `milestones/160-share18-replay-transport/scripts/prefix_transport.py` | `7a0b137ee6c6b008ae7551f339e480cf8ea508e03940ad9edc75ed7244d89fc0` |
| `milestones/160-share18-replay-transport/data/completion.json` | `ad47c5cf9880c90753e5a9f40d5ff63f1b4e49e76f3e254622b9567b9e7e6182` |
| `milestones/160-share18-replay-transport/data/prefix1055/prefix-transport.json` | `8921753b2efaf86b964431f64a776bcefa70c9900a211ec3a3993d4f5f0f0866` |
| `milestones/160-share18-replay-transport/data/prefix1055/checkpoint-after1055.json.gz` | `00e1d41b6d60ba10aae59d9b44332c8c4365b8a3b93421a135c565cfb25673a0` |
| `milestones/155-share17-replay/scripts/emit_full_v2.py` | `83407a0e1526b1c41b4da73f1d9aa6cda0ca09a3b85a8c6c048ff03c1b6df103` |
| `milestones/155-share17-replay/data/full-replay-completion.json` | `d074744dc80ccead20ca771b84a358543a3f7756f0d85a253f03638aa21f3ee6` |
| `milestones/144-countfree-share18/lean/LratFast144.lean` | `f0101d53f2c2651e585f31938e0b5be7b82de49f7ee7c27333b6112116ace56c` |
| `milestones/144-countfree-share18/data/proof-plan-base.json` | `f398fcd7276e16732723e015cd127d2bc372b270912bfa95d68e40c7c866f2ec` |
| `milestones/144-countfree-share18/data/alternative-review.json` | `475e135176575a00a52dd4dd40c7f50c5f6acf24451ab6c21628dcad855229b3` |
| `milestones/144-countfree-share18/data/large-proof-archives.json` | `0691426cdd31801826288728be6f85b553423c05edeebcbd8b68f68556a0162d` |
| `milestones/144-countfree-share18/certificates/share144.lrat` (inherited pin) | `74ab1a039d1476e03cfed0500f95f5f27d5935589942c227ff39315d5bd139d9` |

Scope: source inspection, small JSON metadata, file-size inspection, bounded source prefix inspection and small-file hashing only. No all-proof parse, full graph access, native replay, compiler, solver or accepted-file modification occurred. This report is a design audit; it certifies no additional deduction and claims no new global snake bound.
