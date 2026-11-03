# Milestone 120: final proof receipt review

The bounded independent review passed. All 25 modules in the completed grouped proof run and the subsequent `ReferenceCoverage120` module have successful receipts. The review verified 271 distinct source, compiled-object, log, snapshot and dependency files against their recorded SHA256 hashes, together with direct-import resolution and all 11 printed axiom reports. No compiler, solver, graph enumeration or proof replay was launched during this review.

The immutable review evidence is `data/final-receipt-review.json`, SHA256 `3f4151f5201a14a3f19a317dca34c55a44649bff5a23d496354e1eb632673d6d`. Its reproducible implementation is `scripts/audit_final_receipts.py`, SHA256 `d37b0a7af94cb8517225980b124b489998442fc06e128ca3483859a10454faa4`. The script writes a new evidence file exclusively and refuses to overwrite an existing file.

## Actual-snake theorem

`ActualOuter120.outer_refuted` proves the local exclusion for direction word $012031$ with five intervals

$$
[0,3],\ [0,3],\ [0,21],\ [0,3],\ [0,3].
$$

It composes the checked concrete semantic theorem and checked contradiction. There is no remaining local-contradiction premise and no reference-catalogue refutation premise in this statement.

For an actual snake, a fitting six-transition window starting at $r$ whose canonical direction word is $012031$ therefore satisfies

$$
\alpha_{r+1}\ge4\quad\text{or}\quad
\alpha_{r+2}\ge4\quad\text{or}\quad
\alpha_{r+4}\ge4\quad\text{or}\quad
\alpha_{r+5}\ge4.
$$

The proof uses the existing canonical interval transfer and the general bound $\alpha_{r+3}\le21$. The middle count has no additional restriction. The encoded forward and reverse theorems retain their fitting-window and direction-match hypotheses, require $s\le1$, and exclude the corresponding five-count interval hit inside a nine-transition graph window. The reverse theorem reverses the selected direction slice before canonicalization and uses the reverse interval flag; the symmetric interval list preserves the intended four outer caps.

`ActualOuter120` completed in 11.547 seconds. Its exact pins are:

| Item | SHA256 |
|---|---|
| Receipt | `757f98c8b6cf1aaf0c1f26470ee954a7312b659a3bb9ef3651dc0998c60cf6bb` |
| Source | `9eb3821bb7638e5194c632dd406d92913e9a0b6669c40bda9ba63ef51b0d4f94` |
| Compiled object | `03cc81c3ead62ecf61c75825e186b4f04665b8ea41995a6eb72063b33bd200d9` |
| Log | `041eca9246f5dda87ac01c30e7a6a5eacb15bf66dd93adb1b922f481462568e8` |

The complete 25-module run record is `logs/check-run-1793674102295627900.json`, SHA256 `c24a0928ab07654eaaea1c52883122b40367cf008d7f14a63207c50cf19b37e2`, with status `PASS_REQUESTED_MODULES` and no active module. Reused successful modules were checked against their own preserved source and checker snapshots. The review also verified that the concrete semantic and contradiction imports resolve to the intended milestone-120 objects and that the reference interface resolves to its pinned milestone-85 object.

## Exact reference coverage

`ReferenceCoverage120` completed in 54.813 seconds. Its four checked statements prove the fifteen listed entries refuted, reduce the full union obligation to the filtered remainder, establish that remainder's length as 1363, and identify the three new zero-based indices:

| Index | Directions | Count symbols |
|---:|---|---|
| 126 | $012031$ | $(2,3,6,3,2)$ |
| 127 | $012031$ | $(2,3,6,3,3)$ |
| 138 | $012031$ | $(3,3,6,3,2)$ |

Here symbol $6$ denotes the interval $[6,21]$. Each new entry is narrower than the proved interval exclusion: its four outer counts are at most three, and its middle interval lies within $[0,21]$. The proof uses the existing centre-bound weakening lemma in this direction and appends the twelve already checked entries from milestone 109.

The independent literal check parsed all 1378 union keys, verified the three indices, verified that the fifteen selected keys are distinct members of that union, and obtained exactly 1363 keys after filtering. The checked equivalence leaves the refutation of those 1363 keys as the remaining catalogue obligation; it does not discharge that obligation.

| Item | SHA256 |
|---|---|
| Receipt | `e627ea0a2bf307207e68a952517ede5b63af085cc295a00f8f81da4cdacbe8f7` |
| Source | `c03842cad88cf8e55c6b22f5c86914233c43d4b19c4fa77c1ec4fef2b2f1414c` |
| Compiled object | `d931fac6ad3a53b493d39d19fe22c0b742956389f176b64ba9c34c5f8aa7cad4` |
| Log | `bd6d517eb8063763ac899e0020f3fc27dabf5743d2420db79479ec9e19577e8e` |

## Axioms and limits

The seven reports printed by `ActualOuter120` contain only `propext`, `Classical.choice` and `Quot.sound`; the concrete semantic Boolean check uses only `propext`. The two reference refutation/equivalence statements use the same three standard axioms. The remaining-key count uses `propext` and `Quot.sound`, and the three-index equality uses no axioms. Every printed list agrees exactly with its receipt and log. The reviewed source files contain no `sorry`, `admit` or `native_decide`.

This review establishes integrity and scope of the saved successful checks. It does not repeat Lean checking or native RUP replay. The historical source-only and pending labels in earlier review files remain records of their earlier stage; the two final receipts now discharge those particular pending checks.

No new global upper bound follows from these local results. The separately reviewed graph experiment removes 63 additional keys and leaves its numerical means and ranges unchanged. Its other candidate sum inequalities retain their existing proof status. The finite snake-bank scan and proposed next target were outside this bounded receipt review.
