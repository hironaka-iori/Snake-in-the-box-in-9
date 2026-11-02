# Reference exclusion catalogue audit

Inspected 2 November 2026. This is a bounded source, provenance, and saved-build audit. No new Lean replay or complete dependency rebuild was run. The report covers reference exclusions and the ten completed milestone-72 interval cases; it does not establish full retained-edge membership or a global upper bound.

## Exact reference data

The builder `milestones/70-proof-supported-share-model/scripts/build.py` reads:

- `milestones/54-share-coverage/data/keys_235.json`: 1,287 rows. SHA256 `7f242c8a9218279ce5d1d2d34f9d34a15378efd687b291206e6d52f4dff86411`.
- `milestones/39-audited-bound-236/data/exclusion-catalogue.json`: 732 rows. SHA256 `902ba82c389cd5dcb0748c4d3fd8bbb59b38fd7e31bef6b32bd50787beb215db`.

The first file's ordered directions and lower-bound symbols equal the ordered Lean literals in `work/final_lean/LocalWindowDirKeys6K235.lean` at commit `74ca83db9c218446211d4f24c5e5a07329fdd847`. Every interval in that JSON file is exactly `(s,s)` for symbols 1–5 or `(6,21)` for symbol 6. This equality was checked from the actual Git blob, rather than inferred from a filename.

The second file's ordered rows equal the literals in the locally pinned `milestones/39-audited-bound-236/upstream/work/final_lean/LocalWindowDirKeysR4.lean`. All twelve pinned milestone-39 source/log hashes match `data/upstream-manifest.json`, whose commit is `7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b`.

Applying the builder's exact canonical/reversal key gives 1,287 and 732 distinct representatives, with intersection 641 and union **1,378**. Thus 236 adds 91 reference keys beyond the 235 set. Adding both orientations yields **2,678 distinct oriented (direction word, symbol word) pairs**. The union has the following count-word widths:

| Width | Canonical representatives |
|---|---:|
| 2 | 4 |
| 3 | 43 |
| 4 | 213 |
| 5 | 1,076 |
| 6 | 42 |

No omission or extra reference key was found in this Python/list comparison. This comparison is separate from a Lean proof of the concrete JSON-to-table translation.

## Existing Lean instantiations

At the 235 pin:

- `work/final_lean/LocalWindowDirKeys6K235.lean` defines `dirKeys6K235` as four chunks and `Snake9.LocalWindow.AllRefuted6K235 := AllRefutedList dirKeys6K235`.
- `work/final_lean/LocalWindowDirGlue6K235.lean` proves `allRefuted6K235_of_parts`. It uses `merge6K235_ok`, checked with `decide +kernel`, to combine 358 keys from `dirKeysR4b`, 294 from `dirKeysR4`, and 635 from `dirKeysK6`.
- `work/spectral/stronger/UpperBound235.lean` supplies the closed theorem `Snake9.allRefuted6K235`, applying the glue theorem to `LocalWindow.allRefuted237`, `LocalWindow.allRefuted236`, and `LocalWindow.allRefutedK6`.
- For a member `k`, `Snake9.LocalWindow.AllRefutedList.mem Snake9.allRefuted6K235 k hk` supplies `Refuted (winOf k.1) (boundsOf k.2)`.
- The 236 keys are supplied by `Snake9.LocalWindow.allRefuted236` in `LocalWindowDirUnsatR4.lean`, again with `AllRefutedList.mem` for individual keys. The pinned source assembles 732 certificate roots.

`milestones/51-exact-bucket-pressure/data/contributor/UpperBound235.lean` and the saved 235 audit/replay logs exactly equal their Git blobs at the pin. Their respective SHA256 values are:

- `420a82ea4368ab222f176ce68d8e014c05c8aeb12bf2a59cd7577ff89c806b80`;
- `bba097bf8edde534822cae1cb49a6c1afecc290f101771c5620c5fb407eafd87`;
- `0e843d1cf628d9caadae8f14133b43d2f3197e1816d9d80fb1bff1b207944fe4`.

The saved 235 audit ends with `UpperBound235: ok`, `chain wall time 1493s; exit 0`, and audits of `upper_bound_235` and `verified_interval_191_235` containing only `propext`, `Classical.choice`, and `Quot.sound`. The pinned 236 audit likewise reports exit 0 and these axioms. These are existing contributor receipts. Neither full dependency closure was rebuilt in this audit.

The search paths in the current `79/data/CanonicalExclusions-audit.json` contain **no** compiled `UpperBound235`, `LocalWindowDirGlue6K235`, `LocalWindowDirKeys6K235`, `LocalWindowDirUnsatR4`, or `LocalWindowDirKeysR4` object. Consequently the generic milestone-79 `Refuted` premise has not yet been discharged by an imported closed reference-catalogue theorem in that environment. Source availability and the saved upstream audit should remain distinguished from such an instantiated local build.

## Orientation and saturation obligations

`LocalWindowDirModel.lean` defines `boundOf s` as `(s,s)` below 6 and `(6,21)` otherwise; all catalogue symbols lie in 1–6. `LocalWindowDirBridge.lean` provides `boundOf_symC` and `coreAlpha_le_21` for internal vertices. The canonical- and reversed-symbol exclusion interfaces in milestone 79 can therefore consume the reference theorems once exact key membership has been established.

The builder adds the canonical forward direction word and the canonical reversed word, with the count list reversed simultaneously. Reversing only directions would be incorrect. The 236 predecessor `DirectionWindowBridge5R4.no_forb_window5` already illustrates the correct use of `revSnake`, `dsOf_rev`, and `symsOf_rev`.

Within a nine-direction transition at start r, the represented counts are at r+3 through r+8. A width-w reference rule at offset o examines directions from r+o+2 through r+o+w+2 and counts from r+o+3 through r+o+w+2, where 2 <= w <= 6 and 0 <= o <= 6-w. Each such count is strictly internal under r+9 <= m. This is the domain needed for the bound 21. The six-count base-6 slice expression is `(code // 6**(6-o-w)) % 6**w`.

## Ten completed milestone-72 interval exclusions

`72/data/proof-audit.json` has status `PASS_COMPLETED_CHAINS`; its ten completed cases equal `72/data/proved-model.json`'s applied cases. Every recorded Lean source hash for these completed chains was rechecked against the current file. Each interval below starts at zero; the tuple lists its four upper endpoints.

| Case | Directions | Upper endpoints | Recorded source modules |
|---|---|---|---:|
| 7202 | 01203 | (2,4,5,5) | 548 |
| 7203 | 01203 | (2,5,5,4) | 491 |
| 7206 | 01203 | (3,5,3,5) | 464 |
| 7211 | 01203 | (4,5,2,5) | 85 |
| 7212 | 01203 | (4,5,3,2) | 352 |
| 7215 | 01203 | (4,5,5,1) | 10 |
| 7216 | 01203 | (5,5,2,3) | 148 |
| 7217 | 01230 | (1,5,5,1) | 8 |
| 7218 | 01230 | (1,21,21,1) | 9 |
| 7219 | 01230 | (1,21,21,2) | 14 |

For each N, `lean/CycleExclusionN.lean` proves `Snake9.LocalWindow.CycleWindowN.refuted : Refuted window bounds` and `excluded_in_snake`. `lean/FourCountN.lean` proves the arbitrary-coordinate wrapper `Snake9.LocalWindow.FourCountN.exclusion`. Cases 7218 and 7219 also have returning-direction corollaries. The saved audit records 32 theorem audits in total.

For all ten, successful build records match the present top-level source hashes, and both `CycleExclusionN.olean` and `FourCountN.olean` exist in:

`milestones/72-four-count-proof-closure/build/950fed501ad64859af6f7f46cf3857db`.

Object existence and source-matched build records were checked; no new compiler invocation or full dependency replay was performed. The six pending cases 7204, 7205, 7207, 7208, 7213, and 7214 are excluded from the proved-only model.

`72/scripts/graph.py --proved-only` applies each completed five-direction word at offsets 2, 3, and 4, in both orientations. The forward six-count indices are `offset+j-3`; reversed indices are `offset+(5-j)-3`, for j=1,...,4. Each upper endpoint is below six or equals 21. Therefore a cap below six requires an exact unsaturated count; cap 21 accepts symbol six and uses the internal geometric ceiling. The saved graph metadata reports 50,510 removed edges, leaving 4,947,008 of 4,997,518. These counts were read from the existing model receipt, without rebuilding the arrays.

## Remaining work

Instantiate both reference catalogues in the current Lean environment, prove the exact key/orientation/table membership and slice connection, then instantiate the ten interval rules. Full retention additionally includes the forty recovered short rules from milestones 47–50 and the three history exclusions; those families are outside this audit. After retention, credit interpretation and complete potential replay remain separate obligations. This report does not reduce the currently maintained global interval.
