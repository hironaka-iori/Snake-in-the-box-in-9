# Independent guard-source review

Reviewed 2 November 2026. No source defect was found in the checked slicing, encoding, saturation, or reversal statements. This review does not claim full retained-edge membership or a stronger global bound.

## Reviewed evidence

The following present source, object, and log hashes were compared with their successful saved Lean audit receipts. The five modules contain 28 printed theorem audits. No additional compiler run was started.

| Module | Printed audits | Source SHA256 |
|---|---:|---|
| CanonicalExclusions | 4 | `5d21253e72a72dc74c979e1b7be05491b3415fe56e5a497340e96e920c56780d` |
| CountWindows | 8 | `ec60fb130f2d25f02da27df5052e48caa09c9a9113de7c6ac5e74295604d01a2` |
| BaseSix | 5 | `80165a375439bdb0efacb5ec849d866e55a6817d601896269ebfa1f8899a6a23` |
| ReferenceRetention | 6 | `41d620dbcea53c346adda0423c3b919a4ae4feb449d5a5219a57c4d5eaabcb50` |
| IntervalGuards | 5 | `0f2155192e12863767b7f63d2721f6ea5e16f2ac5bf8ed60ab67f59b027abbd5` |

## Index and orientation checks

For a nine-direction step at r, `sixSymbols` represents precisely the vertices r+3,...,r+8. A count slice of width w at s therefore contains r+s+3,...,r+s+w+2. Its direction slice starts at r+s+2 and has w+1 directions. The hypotheses s+w <= 6 and r+9 <= m put every tested count strictly inside the snake. Both the initial and terminal allowed positions are included.

`actual_code_slice` extracts the same six-count base-6 digits as the builder's quotient/remainder expression. `encode_injective` requires equal lengths and symbols in 1,...,6; these necessary conditions are supplied by `actual_slice_decode`. The `a-1` digit convention is consistent throughout. No count-zero ambiguity enters that use.

For reversed reference keys, `encoded_reverse_exclusion` compares the forward code slice with the encoding of `syms.reverse`; it then reverses the decoded symbol word when applying the reversed-snake theorem. Directions are canonicalized again after reversal. Thus counts and directions are reversed together.

For the milestone-72 filter, put offset=s+2 and j=i+1. With w=4, the Python forward index is offset+j-3=s+i. Its reverse index is offset+(5-j)-3=s+3-i. These equal the two branches of `intervalHit`. All 24 index comparisons for offsets 2,3,4 and the four count positions were independently evaluated. All indices lie in 0,...,5.

`encoded_interval_reverse_exclusion` uses reversed start m-(r+s+2)-(w+1). Its counted position i+1 maps back to r+s+w+2-i, which agrees with `actual_digit` at index s+(w-1-i). The bounds on i and w prevent truncated subtraction from changing the intended index.

## Saturated counts

The equivalence in `truncated_interval` assumes a <= 21, lo <= 6, and hi < 6 or hi=21. These hypotheses are sufficient: a cap below six excludes the saturated bucket, while cap 21 covers every allowed saturated value. Independent enumeration checked all 1,078 combinations a=0,...,21, lo=0,...,6, and hi in {0,...,5,21}. No counterexample occurred. The geometric application obtains a <= 21 from `coreAlpha_le_21` at strictly internal vertices.

The restriction on hi is material. The same predicate with hi=6,...,20 would accept counts larger than hi once truncated; such intervals must not be admitted through this lemma. All ten current milestone-72 intervals satisfy the restriction.

## Concrete interval catalogue

The generated `lean/IntervalCatalogue.lean` was read after it appeared. Its ordered ten literal direction/bounds pairs were independently parsed and compared with `72/data/proof-audit.json`; they agree exactly. Each case invokes its closed `CycleWindowN.refuted` theorem. The resulting forward/reverse retention statements cover s=0,1,2, corresponding to all three Python offsets 2,3,4.

At the time of this review, no `data/IntervalCatalogue-audit.json` existed. The generated source and its template were reviewed, but compilation of this sixth module remains a parent verification step. A subsequent successful receipt can establish these three concrete-catalogue statements; it does not establish the full graph theorem.

`prepare_intervals.py` pins current source/object hashes for the recorded completed milestone-72 chains and recursively includes their local imports. Its receipt explicitly states that this reuses existing source-matched objects and does not perform a clean replay. Preserve that distinction in the round summary.

## Remaining premises and claim limits

`ReferenceRetention` proves a contradiction from an explicit `Refuted (winOf cs) (boundsOf syms)` premise, canonical shape equality, valid symbol range, and encoded-count match. It has not instantiated the 1,378-key reference union or proved concrete table membership. Its filename should not be described as a completed reference-catalogue closure.

The ten-case interval assembly is a genuine concrete family once checked. Other retained-edge filters still require their own assembly: the reference catalogues, forty recovered restrictions, and the history exclusions. Direction/history encoding from earlier milestones and these guard lemmas alone do not show that every actual edge is present in the saved arrays. Credit interpretation and potential replay remain additional obligations.

Paths `work/final_lean/LocalWindowDirKeys6K235.lean`, `LocalWindowDirGlue6K235.lean`, and `work/spectral/stronger/UpperBound235.lean` in the earlier reference audit denote files at Git commit `74ca83db9c218446211d4f24c5e5a07329fdd847`. They do not denote present files in this checkout. In particular, the last path is absent locally. The local reviewed final theorem snapshot is `milestones/51-exact-bucket-pressure/data/contributor/UpperBound235.lean`.

For a later small import step, the pinned `LocalWindowDirKeys6K235` definitions and `AllRefutedList.mem` provide the key-specific interface; the glue theorem combines the three prior `AllRefuted` families. Importing only definitions/glue leaves their refutation premises explicit. Discharging them requires suitable compatible certificate objects or a checked reconstruction, so it should not be presented as an inexpensive complete 235 closure.


## Final verification after the catalogue check

This section supersedes the earlier pending-compilation observation. `IntervalCatalogue` now has a successful receipt, exit code zero, and three printed theorem audits using only `propext`, `Classical.choice`, and `Quot.sound`. Its final source, object, and log hashes were independently matched to the receipt:

- Source: `f0f3a137cb49c74b66a098ab051a9f0c1974acf486b772aa6f7098bff15e2f3f`.
- Object: `7926df863578e6c99a7a29e41261ef9f5544bf1c26607562a33f2ec5c33d6c3a`.
- Log: `da81e7581e84be2c95a34b50f55798aa36d72f4686452090fa080e11a026365f`.

The final source closes the missing parenthesis around the reversed direction list. The checked reverse theorem consequently states canonicalization of the reversed five-direction slice, as intended. The ten literal keys were rechecked against the upstream completed list after this correction. Together with the first five modules, the round has 31 printed theorem audits.

The current interval-support receipt hash matches the compiler receipt. It contains 2,131 pinned objects. The added external `LratFast14` source and object were independently matched to their recorded hashes. The successful compiler search path places the milestone-72 build immediately after milestone-79's own build and includes the external checker directory. This review does not repeat the full hash/read pass over all 2,131 objects or rebuild them; the successful checker performed that pin validation before compilation.

The README's mathematical scope is appropriately limited: the ten interval filters are instantiated without an unproved catalogue premise, reference-catalogue interfaces remain conditional, and the complete retained-array/credit/potential assembly remains outstanding. No new global bound is claimed.

The external-checker reproduction concern was rechecked against the current preparation script. Its final two lines import `runpy` and execute `pin_lrat14.py` immediately after writing the source and support receipt. Thus the documented preparation command includes the inherited checker pin/path; no separate command is missing. The earlier concern arose from inspecting the preceding version and is resolved in the current source. No actionable defect remains from this bounded review.
