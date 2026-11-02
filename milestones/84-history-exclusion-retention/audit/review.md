# Independent review of milestone84 history-exclusion retention

Review date: 2026-11-02. Scope: source review, exact extraction/adaptation comparison, catalogue correspondence, and current source/object/log receipt fingerprints. No solver, compiler, enumeration rerun, or proof job was started. Only this review file was written. The case7302 driver and files were untouched.

## Final result

No unresolved defect remains within the reviewed scope. All eight final modules have matching successful source/object/log receipts, with 38 printed axiom audits. The three actual-snake history-exclusion guards are covered. The initially missing helper was added and freshly checked; the isolated builder-comparison receipt now pins the final sources and its own checker. Full retained-array membership, weight interpretation and global potential replay remain separate.

## Initial finding and compilation boundary (resolved)

No mathematical error was found in the reviewed history recognition, unique realization, count-index, or guard argument. The initial extraction omitted a dependency and prevented the adapted count proofs from compiling: `centresOf_canon` was omitted from `HistoryCountSupport.lean`. The failed initial `TerminalCount.log` reported `unknown identifier 'centresOf_canon'` at its centre-membership step and consequently reports `sorryAx` for `in_snake`. Both other adapted roots use the same lemma. Its original source is milestone65's `lean/CountChoice.lean`, beginning at line65 and ending before `count_choices_in_snake`.

At the initial read, the old `TerminalCount`, `CountPhase04` and `CountPhase29` audit files predated the adaptations: their source hashes fail against the present adapted sources and carry `count_support_sha256` from the rejected import-overlay route. Their `PASS` labels do not certify the new sources. A fresh source-matched successful receipt is required for each adapted root, followed by `HistoryExclusions`. This is a concrete missing-dependency error, not an accepted proof placeholder.

At initial inspection, the matched successful receipts cover `HistoryWindow` (7 audits), `HistoryRealizations` (3), `HistoryUnique` (3), and the first `HistoryCountSupport` version (4), totaling 17 audits. A later resolution section, if present, supersedes this initial compilation status.

## Exact three-pattern coverage

The three exclusion entries in milestone67 `data/full-model.json` and milestone70 `data/enriched-model.json` agree, and all three input hashes in `data/realizations.json` match current files. The generated Lean signatures and words equal those entries in order:

| Rule | Signature | Eleven-direction word | Count digit | Guard |
| --- | --- | --- | ---: | --- |
| 24 | `[139,353,177]` | `01230432543` | 5 | at most2 |
| 1004 | `[460,350,180]` | `01234532013` | 3 | at most2 |
| 1029 | `[460,353,177]` | `01234532053` | 5 | at most2 |

`historyRules` contains exactly these three signature/digit pairs. Builder70's history filter requires a three-ID suffix match and rejects the stated digit cap. `builderHistoryHit` expresses the same length check, last-three extraction, and cap for an actual history/direction/count triple. The final theorem's scope is this specific filter; it does not identify an index in the full retained edge arrays.

## History and realization argument

`emitted_three_actual` derives the essential lower bound `2 ≤ r`; it does not assume this or silently truncate an early history. Its last-three result refers to the actual direction IDs at `r-2`, `r-1`, and `r`. The slice transport then applies to the eleven-transition window starting at `r-2`, whose fit follows from `r+9 ≤ m` and the derived lower bound.

The canonical prefix identity is exact for the first nine symbols. `realization_unique` uses the eleven-symbol length to split off exactly two symbols, proves both lie below9, and applies the finite81-continuation table. The actual-window wrapper supplies the canonical restricted-growth property and inducedness from the snake, and all three canonical slice matches from history. Thus the finite table is applied to every actual compatible eleven-word, without assuming uniqueness from the Python enumeration.

The Python preparation independently compares all11,162 induced canonical eleven-words with its81-continuation search. This review checked its source and receipt input pins; it did not rerun that enumeration. The three Lean finite-table receipts are the checked finite component used by the transport argument.

## Count offsets and saturation

With long-window start `t=r-2`, the first and third geometric theorems give the count lower bound at `t+10=r+8`; the second gives it at `t+8=r+6`. `actual_digit` identifies these with digits5 and3 of the six-count code, respectively, since digit `j` represents `min 6 (coreAlpha p (r+j+3))`.

All three geometric conclusions are `3 ≤ coreAlpha`. Therefore the corresponding truncated digit is strictly greater than2, including when the actual count is saturated at6. No exact-value interpretation of symbol6 is used. No new endpoint, small-count, reversal, or additional local refutation premise is introduced. The IDs and words are oriented, matching the builder's oriented table.

## Compatibility extraction

Mechanical read-only comparison confirmed that the initial support source consists exactly of the stated original text slices with a new common namespace/import header. These contain four theorem bodies (`count_mono`, `forced_absent_plus`, `known_absent_count`, `corners_count`) and two definitions (`forceCheckPlus`, `corners`). Their original source hashes and the generated support hash match `compatible-count-sources.json`.

Each adapted root is exactly its original module after replacing `import CountChoice` with `import HistoryCountSupport` and removing the old open command. All definitions, statements and proof bodies are unchanged. Fresh compilation in the current bridge environment is necessary because changing imports can change name resolution. The missing `centresOf_canon` dependency identified above is precisely such an incomplete extraction, and must be added before claiming the adapted roots checked.

`check.py` puts the fresh milestone84 build first, excludes the rejected overlay via its disabled branch, verifies the compatibility-source pins, and checks the source/object/log receipts of declared local dependencies. The exclusions check additionally validates milestone81's `PositionTransfer` receipt. A successful result will therefore establish the three stated history exclusions using current support, while remaining short of complete retained-array membership, charge interpretation, or potential replay.

## Initial receipt fingerprints

- `HistoryWindow`: receipt `0078c844ad8ad57517b3f800e33ac3c776848e7d2c9325b4adb9ab3f348e99ab`; source `4f68733db1e4a427a6f3dc9f1d770aa74fcc7b0a1a2cf983b439076f51585000`; 7 audits; source matched at this read: True.
- `HistoryRealizations`: receipt `d14d0ecf39116e521d67e386efd832a7f67d34d04d87157b08d03b40995a666c`; source `07dedd43d6bada6cf054f3de913ea2e412c09142a20caeb36f2026d52a07e486`; 3 audits; source matched at this read: True.
- `HistoryUnique`: receipt `231d5a585425bb6ac3de1cdd1525f14370d53faa784ee49647ed8c024b9978f0`; source `8bc4c8fd9515cc0f1be3341af6aad27ba614959a5748f3ec4ebfab58f8bc8010`; 3 audits; source matched at this read: True.
- `HistoryCountSupport`: receipt `21771f7203724afbdfa682e50f4bbbc3a51df6516c9cc62a1229a86d7f9b2128`; source `ef0900349d35cc4be67696af7ac85a7fa799371f8842967d01888cefbeff989d`; 5 audits; source matched at this read: True.

## Isolated builder-filter comparison

The current `audit/check_builder.py` extracts the actual `for pat` loop from builder70's Python syntax tree and executes it with the complete saved pattern list. It compares the resulting acceptance mask against the three Lean signature/digit literals. It also checks the exact75-prefix list and505-extension list against their Lean literals. The present source was reviewed; this independent audit did not rerun the comparison.

The factorization is valid for the inspected loop: a pattern first checks the three-ID suffix, then forms a conjunction of coordinatewise count caps; only exclusion-mode rows change acceptance. The three applicable history/direction pairs are exactly `(43,177)`, `(68,180)`, and `(70,177)`. All37,875 possible history/direction pairs are screened with six uniform count vectors (227,250 tests), then every46,656 six-count code is checked for each applicable pair (139,968 tests). Each applicable pair accepts31,104 codes and rejects15,552 codes. These are counts in an isolated filter comparison before source-shape compatibility and other graph filters. They are not counts of newly removed edges in the actual retained graph.

The parent added the checker itself to the comparison inputs after the provenance recommendation. Final comparison fingerprints must match the final Lean source; a transient mismatch during an arithmetic-simplification edit was observed and is not treated as final verification.

## Dependency repair source check

The generator now includes the exact `canonicalCentres` definition and `centresOf_canon` proof from `CountChoice.lean`, adds its source fingerprint, and prints a fifth helper axiom audit. The newly added source slice was compared with the original and is unchanged. This supplies the previously missing declaration. Fresh receipts for all three adapted roots now match their current source/object/log bytes and the compatibility-source manifest. The final receipt verification below supersedes the earlier pending observations.

## Final dependency and receipt resolution

The corrected support includes the unchanged `canonicalCentres` definition and `centresOf_canon` proof. All five helper theorems, the three adapted count modules, and the final exclusion module now have fresh successful receipts matching current source, object and log bytes. The original root statements, definitions and proof bodies remain unchanged except for their import/open commands. Each successful local dependency receipt hash and each compatibility-source-manifest link was checked. Printed axiom sets are confined to `propext`, `Classical.choice` and `Quot.sound`.

The eight modules contribute 7+3+3+5+5+5+5+5=38 audits. The final `HistoryExclusions.lean` proof adds only arithmetic normalization before the three truncation contradictions; it changes no theorem statement, guard, offset or assumption. Its `actual_builder_history_retained` theorem quantifies over every `Snake m`, every `r` satisfying `r+9 ≤ m`, and all three rules. It rules out exactly the builder's corresponding history hit at the actual history index, actual direction ID and actual six-count code.

The refreshed filter comparison has nine input pins, including its own checker and the final exclusion source. Every pin matches the current file. Its isolated-test counts and mask claims remain distinct from full-graph edge counts. The rejected original import-overlay preparer and metadata have been moved to `diagnostics/`; the current compiler script no longer contains the unreachable old overlay branch. Their earlier receipts are not used for the final claim.

No new local share theorem, complete graph walk, array-index existence, edge-weight lower bound, finite-potential replay or numerical upper bound is established by these history guards. Existing inherited support was hash matched and reused, not rebuilt from its full transitive closure. This review inspected the final successful receipts rather than rerunning Lean or the comparison.

Final receipt fingerprints:

- `HistoryWindow`: `0078c844ad8ad57517b3f800e33ac3c776848e7d2c9325b4adb9ab3f348e99ab`; 7 audits.
- `HistoryRealizations`: `d14d0ecf39116e521d67e386efd832a7f67d34d04d87157b08d03b40995a666c`; 3 audits.
- `HistoryUnique`: `231d5a585425bb6ac3de1cdd1525f14370d53faa784ee49647ed8c024b9978f0`; 3 audits.
- `HistoryCountSupport`: `21771f7203724afbdfa682e50f4bbbc3a51df6516c9cc62a1229a86d7f9b2128`; 5 audits.
- `TerminalCount`: `2ab06e32ab0c9b0c675f0c25e62e0ca8677dc7f240ba78888115990cb1aa9b1e`; 5 audits.
- `CountPhase04`: `34998a80adab1a5c4fe85000a98e57b9384b638eb4959d3a329d3c9d5870d1f7`; 5 audits.
- `CountPhase29`: `750f2b3e9917406bc8ae8df4763a00e5ec8e47a590453c5ff0fea6769e4c00fc`; 5 audits.
- `HistoryExclusions`: `0feca227e9fd7a9976dad7a3da0e0a68324aed3fd90488d519e3d436a43aa7bf`; 5 audits.
- `compatible-count-sources.json`: `353ca8fb44e43d196deac1b50c224a158de4c81aa80d3825521e4d136b7b4f0e`.
- `filter-comparison.json`: `fc220000f11931edfb32ca3420a8c7144a787d160118d702aa91913993376ec3`.
- `realizations.json`: `4a5ac12436bd68f08094c5cf7c6442ea2ac41a772cd8c260267ec9ad410803ac`.
