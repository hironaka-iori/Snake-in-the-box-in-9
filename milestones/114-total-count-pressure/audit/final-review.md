# Final independent review of milestone 114

The final evidence consistently records a completed native contradiction for the selected total-at-most 18 formula, with concrete Lean certification still pending. No substantive defect was found in the reviewed replay logic, clause-ID mapping, pinned artifacts or final mathematical note. This review inspected the checker and existing evidence; it did not repeat the 22,088,504-hint propagation replay, run a solver or compiler, or modify earlier reports.

## Change since the earlier native-core review

`audit/native-core-review.md` and `data/native-core-audit.json` describe the earlier state, when the full-formula, conversion and extracted-core LRAT attempts were all incomplete. Their statements about those three artifacts remain correct. They predate the successful system-temporary-storage run and must not be read as the final status of the selected formula.

The new run used the same 5,431-clause core, original literal ordering, solver executable and options, then copied the proof back with matching hashes. It returned exit 20 with an UNSAT message after 20.656 seconds and saved 212,391,180 bytes. I verified that its first 40,935,424 bytes equal the entire prior extracted-core timeout artifact. This is exact provenance evidence; the elapsed-time difference is not a controlled storage-performance measurement.

The successful solver record remains labelled `UNSAT_LRAT_UNCHECKED`, accurately describing that stage. The subsequent selected-certificate record has the stronger status `NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING`. These records describe different verification stages and are compatible.

## Selected certificate and replay logic

The selected dependency trim uses **5,206 original input clauses, 358,464 deductions and 22,088,504 propagation hints**. The full native CNF still contains 55,860 clauses. The raw proof, both trimmed proof files, full CNF, generator, replay script and source metadata hashes match their saved pins.

The reviewed `replay_core.py` establishes each added clause by assuming its literals false, following only positive references to earlier clauses, accepting unit propagation or a conflict, and requiring a conflict before storing that clause. Referenced clauses must exist in its database; unsupported negative RAT hints are rejected. Deduction IDs strictly increase. The last stored clause must be empty, and the deduction/hint totals must equal the trim counts. Retaining previous clauses after dropping deletion records is sound for these RUP checks because the retained earlier clauses are already justified.

The first replay uses the 5,431-clause core's input numbering. The second uses the full CNF's numbering. An input ID $i\le5431$ maps to its recorded original input ID; a deduction ID maps to

$$
55860+i-5431.
$$

Thus new deductions remain above all original input IDs, with their order preserved. I rechecked all 5,431 original-clause identities and uniqueness of their input IDs. The 5,206 selected original IDs are unique and belong to that mapping. I also compared 16 mapped records, eight at each end, without replaying their propagation hints. Both final records contain the empty clause: local ID 495804 and full-CNF ID 546233. The full-file hashes verify the exact artifacts whose complete replay is recorded.

The source runs the same RUP checker twice, once in each identifier system. This checks the mapping through replay; it should not be described as two independent checker implementations. The present review is a source-and-provenance audit of those completed runs, rather than a third complete propagation replay.

## Unselected cycle-pool trial

The alternative trial uses 115 pooled cycle cuts, including the original eight. I independently checked all 115 listed sets for containment in the current radius-four region, distinct vertices, connectedness and induced degree two. They are valid induced-cycle exclusions.

Its trimmed proof has 339,801 deductions but 29,534,822 hints, more than the selected proof. `pooled-trim.json` explicitly records `TRIMMED_POOLED_PROOF_NOT_REPLAYED`, and its proof hash matches. It remains an unselected, unreplayed alternative. Smaller deduction count alone does not establish lower replay cost; the larger hint count supports retaining the existing selected certificate for the next stage.

## Helper theorems, graph evidence and final note

The successful receipts for `TotalGeometry114` and `Comparison114` remain unchanged: two modules and four printed axiom reports. `TotalGeometry114.actual_total_sum` retains its explicit local-contradiction premise. The three arithmetic lemmas establish comparison equivalences and the obstruction at slope at most $2424/5$; they supply no local contradiction or graph-coverage assertion. Concrete sum-counter semantics and Lean replay are therefore still needed before closing the actual-snake total-count theorem.

The final mathematical note agrees with the saved graph experiments and cycle audit: total19 removes 2,263 additional keys beyond 113, with completed mean/range $2424/5,2881/5$; the hypothetical total20 removes 8,030, with $2424/5,565$. Both conditional profiles remain at mean 496 and range 602. Integer comparisons remain 235 and 234. Total20 has only an `UNKNOWN` local probe. All four saved cycles have zero deficits for the existing nine-rule family, so the stated coefficient ceilings remain valid within that family. No graph calculations were repeated in this review.

The note correctly distinguishes completed source share floors from the newly assumed count restrictions. Its maintained 191-through-235 interval is inherited from the contributor proof and archived audit, as stated there; it is not a new consequence certified in milestone 114. The final note also correctly identifies 012345 as the common later test shape, while leaving those exact cells untested.

The next useful work is reducing the selected certificate and exporting/replaying it in Lean with the existing sum-counter semantics. The counter must retain all 105 literal occurrences, including repetitions among 84 distinct literals. After that obligation advances, the recorded 012345 cells provide a bounded local-search continuation. The final note makes no new upper-bound or optimum claim.

## Final pins

Paths are relative to `milestones/114-total-count-pressure`.

| Artifact | SHA-256 |
|---|---|
| `data/012310-total18-certificate.json` | `50944a610c60a231b361cbc50def49664ad8f98d7e9d53f2dae67cde61155e75` |
| `data/extracted-core-scratch-solver.json` | `e4dd95d39b1cc175c457938d5b7204af114455bf9fba1d7e5532fa6cf2c93798` |
| `scripts/replay_core.py` | `ada1b3afed16d7ae053674a9803c2c51b6812402537a353b92df3992b509a5ce` |
| `data/proof-summary.json` | `9289c3ec78a31ea9b7f33007ea7dd01de67f0e48cb3c88fd5155591a6cb7ade9` |
| `mathematical-note.md` | `0301d31145e447e40b5eafd911c9ac29c3c6fe2e6aced04632ee3142706504a5` |
| `data/cycle-audit.json` | `fc245e6a30bb01b820434437bb8c20fc3c46f5d4016e7da7567618722d3e1eda` |
| `data/pooled-trim.json` | `e5b031301d97fbc733faa2efe0bd32305912366f4b0fbcd4a687e3894ab3aca2` |
| `data/TotalGeometry114-audit.json` | `6975b1a3057a32d3bbd6327a184afc4b87f2630cc10c0ee3810933c163a25d6b` |
| `data/Comparison114-audit.json` | `5fd98f970998fa205ba40a8f7e0a98690f9d48e3cfa7c09a1aee864849871954` |
| `audit/native-core-review.md` | `c43af7223afb16b3a63545369075edc582066d667b448929ebc9d70380db5c8a` |
| `data/native-core-audit.json` | `6fd66ccb4625052a66baac02fe4c4fa8a3f00485f84a663ff4b1021fbeb7e03c` |

The selected raw proof hash is `9359aa6d27a8ae04f0bb72ee73afe9b2e99368fa79a8095b07f221a634e93103`; the core-numbered trim hash is `4a6824216f6ba5d8a43ea7da646c4e55108b811ade06a17a50ba21dd3ad5e839`; and the full-CNF-numbered trim hash is `bd62c3efa8171c8a440a976bdb3fa9c27eb02d316d3e15dadb05ce57e99ab233`. All were checked against the retained original files during this review. Archive compression and packaging were outside this review's scope.
