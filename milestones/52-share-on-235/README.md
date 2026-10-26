# Milestone 52: empty-square shares against the 235 baseline

Research round 6 of 10 after manuscript revision 46. This continues route 1, empty-square charging. The next scheduled paper revision is milestone 56.

## Local theorem and verification status

For six distinct consecutive directions `(a,b,c,d,e,f)`, suppose the five internal singleton-square counts are `(3,A,2,3,B)`, where `6 <= A,B <= 21`. Their integer empty-square shares at resolution 12 sum to at least **96**.

The share of a selected vertex x is the sum of `floor(12 e0(q)/dS(q))` over its nine neighbours q. The integer e0(q) counts empty square faces incident to q; dS(q) counts its selected neighbours. The denominator is positive in every term because x is selected.

Verification is complete: [data/verification.json](data/verification.json) reports **PASS**, with **59 Lean modules and 12 dependency audits**. The audits contain only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The checks cover the clause interpretation, the replay, and the theorem for arbitrary coordinate labels. The ordinary radius-four model has a saved acyclic witness with share 307, so this certificate supplies genuine share information. No full-snake attainment or sharpness of 96 is asserted.

The native formula has 445,111 clauses and 38,819 variables. Its trimmed core has 7,208 clauses, 5,191 active variables, and 8,960 semantic variables. The Lean replay has 382,890 hints. Four semantic assignments, including the matching local witness and three complete bank snakes, are checked against all 445,111 clauses. The matching witness fails exactly the imposed share-cap clause.

## Effect on the current finite model

The contributor's completed 235 proof supplies 1,287 exclusions, pinned to commit `74ca83db9c218446211d4f24c5e5a07329fdd847`. Adding these to the previously checked local rules removes 363,788 further transitions, leaving 3,061,188. The complete contributor dependency closure was not rebuilt locally; its theorem and successful saved Lean audit were reviewed in milestone 51.

Both the checked share48 rule and the earlier numerical share96 rules leave the normalized minimum mean at **4**, with a twelve-edge attaining cycle and a verified potential loss of 5 count units. The complete critical family has 68,238 edges, 15,982 states, and 2,499 distinct five-centre windows.

Testing the seven windows of the saved cycle at share cap 95 gives five numerical INFEASIBLE results and two UNKNOWN results. Ordinary controls subsequently return UNSAT for all seven. Those share tests therefore do not establish a distinct empty-square obstruction. Applying the five numerical bounds still leaves mean 4, with a replacement three-edge cycle.

The search was redirected to windows with ordinary positive controls. There are 127 such windows in this critical family. Testing the twelve most frequent at share cap 95 yields six numerical INFEASIBLE and six UNKNOWN results. The first is the share96 theorem above; the other numerical results have no Lean replay in this round. Its pattern occurs 476 times on the critical edges. This does not establish an occurrence frequency along an arbitrary snake.

Combining all previously saved numerical count/excess rules with the contributor's exclusions also leaves mean 4 on 2,962,663 edges. All four reported graph means have independently checked integer potentials and attaining cycles. The graph-to-snake coverage proof for these local generated models is still pending. No new global bound follows from this round.

## Exact empty-square target

Write m for the number of snake edges, T for the total singleton-square count, and s0 for the number of empty square faces. The incidence identity is

`T + 2 s0 + 35(m+1) = 9214`.

The contributor's six-centre estimate uses `4m <= T+21`. Retaining the empty-square term gives

`39m + 2 s0 <= 9200`.

Consequently **s0 >= 18 suffices for m <= 234**. This threshold is exact for this inequality: m=235 is consistent with s0=17 and inconsistent with s0=18. These implications are checked in Lean under the stated incidence and count hypotheses; this round does not provide a newly assembled Lean bridge from the contributor's entire theorem to the retained identity.

At resolution 12, the global share sum S satisfies `S <= 48 s0`. Thus nine disjoint occurrences of the new share96 window would suffice. With arbitrary five-centre windows, each snake position belongs to at most five windows, and 43 qualifying occurrences would suffice instead. The numerical implications are checked under their explicit share-budget premises. Neither required occurrence count is proved.

## Most confident next step

Core inspection shows singleton-bound clauses only at the first, third, and fourth centres. No bound clauses from the second or fifth centre occur. This suggests the stronger statement with counts `(3,A,2,3,B)` for unrestricted internal counts A and B. The current theorem still assumes `6 <= A,B <= 21`.

Removing those restrictions would simplify the theorem. However, a subsequent scan of the complete current critical family finds only the existing truncated pattern `(3,6,2,3,6)`. This generalization alone would not add a critical-window occurrence in that model. It is retained as a proof-development lead; the immediate range-pressure priority is covering the remaining minimum-charge cycles. Merely changing the bound list would invalidate the current counter checks; the interpretation must be updated too. The evidence is recorded in `data/core-dependencies.json`.

## Structure and reproduction

- `lean/`: local share theorem, certificate replay, and conditional empty-square target arithmetic.
- `certificates/`: losslessly compressed formulas and proofs; `data/archives.json` records hashes.
- `checked-share/`, `exploratory-share/`, `cycle-share/`, `combined-share/`: separate finite-model evidence with distinct premise sets.
- `data/supported-critical-windows.json`: the 127 critical patterns with existing positive controls.
- `data/share-screen/` and `data/supported-screen/`: the two numerical screening batches.
- `scripts/verify.py`: checks the exact core, archives, Lean source hashes and audits, positive controls, and every edge of all four potential certificates.
- `scripts/replay.py`: dependency-aware Lean replay using the existing local support builds. `--resume` retains only successful source-hash-matching records; it is not a clean-machine bootstrap.

The interpretation is split into 29 clause checks plus counter and totalizer checks. `scripts/split_semantics.py` creates this decomposition after `scripts/export_share.py`; a general checked append lemma assembles exactly the original clause list. The replay uses a 64 MiB Lean thread stack for the final expression equality check. An interrupted monolithic run is not counted as a successful proof.

The contributor-checked interval remains **191 <= a(9) <= 235**. The paper and its editor mirror remain unchanged at the previous 236 revision until the scheduled rewrite. Authors and hyperlink settings are preserved.
