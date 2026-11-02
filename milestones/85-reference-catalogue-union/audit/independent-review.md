# Independent review of the reference catalogue union

## Result and scope

No concrete mathematical or data-selection error was found in the inspected sources. The catalogue arithmetic, direct source witnesses, bucket semantics, and forward/reverse window placement agree. The executable comparison provides an exhaustive check of the isolated filter over its stated direction/count domain, with an independence limitation described below. Neither this comparison nor the conditional Lean interface establishes full graph retention or a global snake bound.

This was a bounded source/data review. No Lean compiler, solver, full comparison rerun, Git operation, or active case7302 process was invoked. Only this report was written. The existing chunk checks were still running during inspection, so the receipt snapshot below does not assert completed checking of the full union theorem.

## Catalogue and selection checks

Read `scripts/prepare.py`, `scripts/generate_chunks.py`, `lean/ReferencePicks.lean`, `lean/ReferenceUnion.lean`, `lean/ReferenceInterface.lean`, and `audit/check_builder.py`. Independently parsed the two preserved upstream key sources, the saved union rows, and all 22 generated Lean key and pick lists.

Verified:

- The two normalized catalogue sizes are 1,287 and 732; their intersection has 641 elements, giving 1,378 union representatives.
- All 1,378 representatives occur directly in the preserved source catalogues. The selected witnesses use 1,287 entries from the 235 catalogue and the additional 91 entries from the 236 catalogue. Every saved source index selects exactly the stated directions and symbols.
- Each representative's direction word is canonical, its number of count symbols lies between 2 and 6, and it has one more direction than count symbols. Every symbol lies in 1 through 6.
- Width counts are 4, 43, 213, 1,076, and 42 for widths 2 through 6 respectively.
- The union of both orientations has 2,678 distinct direction/count pairs. Reversal changes both direction order, followed by canonical relabelling, and count-symbol order.
- Every generated chunk key list equals the corresponding direct source selections; concatenating the 22 lists reproduces the sorted union exactly.

`prepare.py:27` checks the 235 JSON intervals before replacing each interval by its symbol. Lines 29–30 require exact ordered agreement with the pinned Lean source lists. Lines 36–39 check union cardinalities, direct representative availability, and oriented cardinality. The parser is a finite-data parser for the present literal format, rather than a general Lean parser; the exact lists and the generated selection proofs are the relevant safeguards.

`ReferencePicks.lean:8–10` maps `false` to the 235 source and `true` to the 236 source. `pickValid` requires an in-range index before `pickKey` membership is used, so its default empty key cannot silently justify an invalid pick. Each generated chunk proves the index bounds, key-list equality, key validity, and source coverage. `ReferenceUnion.lean` assembles these coverage results. Its current Lean statements prove coverage and length; the exact set-union equality and completeness of the normalization are checked by the pinned Python data comparison, rather than expressed as a separate Lean set-equality theorem.

## Count buckets and window indices

`work/final_lean/LocalWindowDirModel.lean:26–29` defines a symbol below 6 as an exact count, and symbol 6 as the interval [6,21]. `ReferenceInterface.keyValid` restricts symbols to 1 through 6, eliminating the otherwise broader branch of `boundOf` for symbols above 6. Thus no catalogue symbol is interpreted as an exact count of 6.

For a window starting at direction index r, the six-symbol code represents counts at vertices r+3 through r+8. A width-w filter beginning at count offset s uses the w counts at r+s+3 through r+s+w+2 and the w+1 directions beginning at r+s+2. This agrees among:

- builder70 `build.py:36–39`, which slices directions as `ds[s+2:s+w+3]` and selects the corresponding base-six digits;
- `ReferenceInterface.lean:43–49`, which takes the same direction slice and the same quotient/remainder count code;
- milestone79 `CountWindows.actual_symbol_slice`, `actual_code_slice`, and `ReferenceRetention.actual_slice_decode`, which connect those positions to actual snake counts.

The hypotheses `r+9 <= m`, `2 <= w`, and `s+w <= 6` ensure every direction and interior count position used by the window is valid. They also prevent the exponent `6-s-w` from becoming a truncated negative subtraction.

The reverse predicate reverses the selected w+1 directions and canonicalizes them, while matching the unreversed code slice against the encoding of the reversed w symbols. This is equivalent to testing the reversed window and reversed count sequence. `encoded_reverse_exclusion` invokes the reversed-symbol lemma, whose actual-snake transport uses `revSnake` at index `m-r-n`; the reversal is justified for an actual snake and does not assume that an independently reversed refutation was already present in the catalogue.

The actual count upper bound of 21 is inherited from the existing snake-count bridge. The new interface adds no exact-six assumption, endpoint condition, or new count-cap premise. Its reference-refutation premises remain explicit.

## Executable comparison and independence limits

The current saved receipt reports:

| Quantity | Value |
|---|---:|
| Direction shapes | 505 |
| Six-symbol count codes | 46,656 |
| Candidate direction/count pairs | 23,561,280 |
| Applicable direction-window placements | 7,278 |
| Accepted pairs | 3,899,352 |
| Rejected pairs | 19,661,928 |

The accepted and rejected counts sum to the stated candidate domain. They are isolated-filter outcomes, not counts of newly removed full-graph edges or history-duplicated edges.

`audit/check_builder.py:9–11` extracts and executes the actual builder's width loop. Its expected mask obtains digits explicitly and folds each chosen digit slice into a base-six integer (`:39–44`), whereas the extracted builder uses division and remainder. This supplies a meaningful independent check of count-digit extraction across every code and every allowed width/offset. Exact generated Lean key literals are parsed and compared to normalized input keys (`:25–32`). All 31 recorded comparison input hashes matched current files during review, and the saved compressed-mask hash matched the receipt. The exhaustive computation itself was not rerun.

The comparison has a narrower independence boundary for direction semantics: both sides use the same canonicalization helper, the same conceptual orientation-table expansion, and the same direction offset expression (`:24`, `:31`, and `:51`). A shared mistake in those conventions could survive the Python equality check. The checker also hashes `ReferenceInterface.lean` without executing its hit predicates. Therefore the semantic alignment to `forwardHit` and `reverseHit` rests on the source comparison above and the Lean window lemmas; it is not independently established by the Python mask comparison alone. No inconsistent offset or reversal was found in that source review.

The comparison injects reconstructed tables into the extracted width loop; it does not execute every part of the builder, its other filters, history duplication, or graph assembly. The manually inspected current builder table construction at lines 22–25 agrees with the checker. Its isolated scope is accurately stated in the receipt.

## Receipt snapshot

All source, object, and log hashes for the following available successful receipts matched the files during inspection. Recorded local dependency receipt hashes also matched, including the inherited milestone79 `ReferenceRetention` receipt used by `ReferenceInterface`.

| Module | Printed theorem audits | Receipt SHA-256 |
|---|---:|---|
| LocalWindowDirKeys6K235 | 0 | `133a504770ddc7c537e0ab55f741eb16811a43f4190c5dbc6a202a19643be1c9` |
| LocalWindowDirKeysR4 | 0 | `6460bb4ef5e63f5d5163c9579fe2ec66a1529a4b22e6fb1b32fde7e4d8fb412b` |
| ReferenceInterface | 7 | `7798ecdfb50ff309c97764c459ca4b8c0eb138bc733dd79ccfcf2fd42f90aa92` |
| ReferencePicks | 3 | `fc585026c35078509e62e1ff85a66c6af0dbfc6b5c815a93a0785c4975a9deb0` |
| ReferenceChunk00 | 4 | `a8651630f6163dacdfa013c1089fe23192b83d9d27e5b91003aaac981cdb6d2a` |
| ReferenceChunk01 | 4 | `3d33eb7346d1b93a1b3d157ab3bf28b4e35d1bdc3a66807e19b8e6a606b68036` |
| ReferenceChunk02 | 4 | `24a7c13fa35af96aa76b0aa886345030fc2034b575ca12351c2711df1d1cac15` |

At this snapshot, chunks 03–21 and `ReferenceUnion` had no success receipts yet. Their source statements were reviewed, but this report does not promote them to checked results. Later successful receipts can supersede this timing limitation without changing the inspected theorem scope.

Comparison receipt SHA-256: `1ee861bf921cf0c62a850f57a153727357d60d3fe5326fae629651be99866eea`.

Uncompressed mask SHA-256 recorded in that receipt: `3d190779411be9070c2cd108ea1d1a150e234b280e8a8e5ddba810af7295f0a7`.

Compressed mask SHA-256 verified here: `ad39a55df219810e2e48744d005bf96106e8078a9cf0059d4e8ebf302790589d`.

## Strongest justified scope

The checked generic interface proves that covered keys cannot match the designated actual-snake windows, conditional on `AllRefuted6K235` and `AllRefuted236`. The generated full-union theorem retains those same two premises explicitly at `ReferenceUnion.lean:39–46`; its pending check status at review time is stated above.

The new key-data objects do not close those premises. The saved historical 235/236 audit logs and the absence of locally importable closed refutation objects are distinguished in `audit/catalogue-provenance.md`. Full retained-array membership, all other filters, weights, potential inequalities, and a global bound are outside this review and are not consequences of the isolated comparison alone.
