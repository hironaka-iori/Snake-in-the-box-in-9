# Q9 critical-family and count-exclusion research snapshot

Published on the separate branch `RamseyCheck`, based on `research/q9-global-cuts-lean-audit` at792c9f80794cad7205d12c8b2b73f69e258225e3. Snapshot publication date:1November2026; source experiments and reports are dated31October2026. This addition is isolated under `work/peer-research-20261101/`.

## Verified local results and limitations

- Three original-geometric count-window UNSAT certificates, with complete CNF/LRAT and original-row/variable provenance:353,1264 and284 RUP steps. A fresh independent reader checks all hints, source reconstruction and declared count hypotheses, and rejects a deliberately bad hint. They are NOT freshly Lean-kernel-checked theorems.
-431 direction-history exclusions, independently checked using all nine coordinate choices. The reviewed sparse direction-history lift and all required frozen data are included.
-Three new count exclusions remove24 additional records from the explicit retained frozen critical subset. Two cyclic components still attain exact mean480. NO new global numerical upper bound is proved, and the complete current5-million-edge graph was not independently rebuilt here.
-This snapshot does not complete KEEP=96, the global snake-to-automaton formal bridge, or full Lean graph-potential replay.

The auxiliary share searches were dependency-audited: the three reported final refutations do not use their share caps or auxiliary face clauses. Report them as ordinary count exclusions. The exploratory share16/32/64 consequences under the original impossible antecedents are vacuous; do not count them as independent nonvacuous share improvements.

## Start here

- [Detailed continuation report and reproducibility notes](work/critical-family-continuation-20261031/README.md)
- [Full geometric interpretation of the first count exclusion](work/critical-family-continuation-20261031/COUNT_WINDOW_PROOF.md)
- [All three standalone certificates](work/critical-family-continuation-20261031/count_window_certificates/)
- [Latest six-page PDF](reports/Q9_Critical_Family_and_Count_Exclusions.pdf)
- [Earlier critical-cycle proof PDF](reports/Q9_Critical_Cycle_Upper_Bound_Update.pdf)
- [Graph-pruning solver and prior independent review](work/graph-pruning-20261031/README.md)

From this directory, Python3.12+ without `-O`:

```sh
python work/critical-family-continuation-20261031/verify_count_exclusions.py
python work/critical-family-continuation-20261031/verify_frozen_data.py
python work/critical-family-continuation-20261031/review_short_closure.py
```

The primary verifier pipeline uses the standard library. The exact original encoder, pure-Python solver/checker runtime, bank fixture, frozen graph records and potential are included at the expected relative paths. Figure/PDF regeneration additionally requires Pillow/ReportLab and the documented Windows fonts. No native Lean/SAT executable or downloaded toolchain is included.

`SOURCE_MANIFEST.json` records exact SHA256/byte identities. Historical experiment manifests and report text preserve their original scope/status; their references to a locally prepared/not-uploaded snapshot describe that historical experiment, not the publication status of this directory. Some experiments are explicitly UNKNOWN or budget-limited and must remain so. All substantial intermediate graphs and proof records from the three new research directories are retained; no compiled Python caches or transfer-only intermediates are committed.

Root README, COLLABORATION, paper and maintained upstream proof modules are unchanged. No merge or global-bound claim is part of this upload.
