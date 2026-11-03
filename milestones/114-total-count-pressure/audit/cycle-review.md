# Independent review of the total-count experiments

The bounded independent audit passed for both saved experiments. It checked 36 cycle-edge occurrences, their full direction/history/count keys, exact graph endpoints and weights, and 648 rule/placement evaluations. It ran no solver, Lean compiler, graph optimization, or full-edge inequality scan. The output JSON and reproducing script are saved separately and refuse to overwrite existing output.

## Evidence and mathematical scope

The total-at-least-19 candidate is supported by a native `UNSAT_UNCERTIFIED` probe for total at most 18, with eight added cycle cuts. A concrete checked refutation is not established by this review. The stronger total-at-least-20 candidate has only an `UNKNOWN` probe for total at most 19, with eleven cuts. Its experiment is expressly hypothetical and supplies no UNSAT support for that inequality.

Both experiments use nine rules. For each rule the audit checked the corresponding saved probe's status, direction shape, complete count bounds, selected sum positions and tested threshold. The existing 113 pair rule and other unresolved rules remain assumptions of these experiments. A profile named `completed` uses the completed baseline share floors; that name does not certify the newly added sum rules.

| Experiment | Profile | Cycle length | Cycle mean | Potential range | Comparison | Integer part |
|---|---|---:|---:|---:|---:|---:|
| Total19 | Completed floors | 10 | $2424/5$ | $2881/5$ | $5517073/23424$ | 235 |
| Total19 | Conditional floors | 8 | $496$ | $602$ | $551765/2348$ | 234 |
| Hypothetical total20 | Completed floors | 10 | $2424/5$ | $565$ | $5517017/23424$ | 235 |
| Hypothetical total20 | Conditional floors | 8 | $496$ | $602$ | $551765/2348$ | 234 |

The comparison was recomputed exactly as

$$
\frac{1098960d+8p+R}{4200d+p},
$$

where the cycle mean is $p/d$ and the stored integer potential has range $R$. The completed total20 experiment reduces that range by $56/5$ while leaving its mean and integer comparison unchanged. These are restricted finite-graph results under the stated rules, without a new actual-snake bound.

The original graph has 4,947,008 keys. Total19 retains 4,865,603 and removes 81,405, including 2,263 beyond the 113 pair-rule experiment. Hypothetical total20 retains 4,859,836 and removes 87,172, including 8,030 beyond 113 and 5,767 beyond total19. The saved removal lists are duplicate-free, in range, nested as expected, and agree with the reported cardinalities and summed marginal removals. This audit checked those sets and counts; it did not recompute each removal predicate across all graph edges.

## Full-key, potential and orientation checks

Every saved cycle key was checked against the source graph arrays and independently accepted by the saved six-digit decision diagram. The diagram, class roots, context assignment and direction words were also compared with the corresponding Lean literals. Endpoint indices and original weights were reconstructed from the geometric, history and conditioned-credit source models, preserving the full $(d,q,c)$ key and raw state numbering. Every cycle closes and avoids its experiment's removed keys.

Each compressed potential was hashed, decompressed, checked against its recorded uncompressed hash, and checked to have the correct number of states, minimum 0 and reported maximum. All saved cycle edges have zero potential slack. The experiment scripts contain an all-edge integer inequality assertion; their exact source and inputs are pinned. This independent audit did not repeat that full-edge assertion, so its direct verification establishes the saved cycles, potential bytes/ranges and arithmetic, rather than independently recertifying the global minimum mean.

The two eligible placements are `word[s+2:s+8]` with count slice `digits[s:s+5]`, for $s=0,1$. The latter is the credited suffix at actual centres $r+4,\ldots,r+8$. Deletions use both placements; extra credit uses only $s=1$, taking the maximum applicable credit. All bounds and selected position sets are reversal symmetric, making the implementation's comparison with the minimum canonical forward/reverse shape valid without reversing its count array. The audit independently reverses counts when displaying a reversed canonical window.

Symbol 6 means $[6,21]$. A rule applies only when that entire interval fits its count bounds. A positive clipped deficit is deleted only when every count participating in its sum is below 6; otherwise its suffix deficit can receive excess credit. All counts in the saved cycles are below 6, so every tuple reported below consists of exact counts. Every applicable rule has deficit zero on both placements of all 36 edge occurrences, and every reported bonus is zero.

These zero-deficit cycles remain unchanged under any nonnegative reassignment of the existing rule coefficients. Thus they give coefficient-independent upper ceilings $2424/5$ and 496 on the respective finite minimum means for this fixed deletion/rule family. The balanced coefficients 24 attain the reported ceilings according to the pinned native all-edge checks. Further coefficient tuning alone cannot improve those means within this family.

## All 012310 and 012034 suffixes

The following rows give all such suffix occurrences on the completed cycles. The tuple is in the displayed canonical direction orientation. Paired edge numbers indicate total19 followed by hypothetical total20; a single edge is shared.

| Edge or edge pair | Shape | Five counts | Total |
|---|---|---|---:|
| 3480444 | 012034 | $(5,3,3,5,4)$ | 20 |
| 1617381 | 012310 | $(5,3,3,5,5)$ | 21 |
| 232890 | 012034 | $(3,3,5,5,4)$ | 20 |
| 3361413 | 012034 | $(3,4,5,5,3)$ | 20 |
| 1609178 | 012310 | $(5,5,4,3,3)$ | 20 |
| 240691 / 212087 | 012034 | $(5,4,3,3,5)$ | 20 |
| 1794998 / 1777187 | 012034 | $(5,4,5,3,3)$ | 20 |
| 732287 | 012310 | $(3,5,4,5,3)$ | 20 |
| 4450869 | 012034 | $(5,4,5,3,3)$ | 20 |

The total19 conditional cycle has the following six relevant suffixes.

| Edges | Shape | Five counts | Total |
|---|---|---|---:|
| 735008 | 012310 | $(3,4,5,4,3)$ | 19 |
| 733502 | 012310 | $(3,5,3,5,3)$ | 19 |
| 4450629,1818081 | 012034 | $(4,5,4,3,5)$ | 21 |
| 1820301,4450804 | 012034 | $(5,3,5,3,4)$ | 20 |

The hypothetical total20 conditional replacement cycle has no 012310 or012034 suffix. Its shapes are 012345,012304 and012301. Strengthening only the 012310/012034 suffix rules cannot directly affect that particular cycle.

## Common remaining test target

The only suffix shape common to all four saved cycles is 012345. Its exact counts are:

- Completed cycles: $(4,3,3,5,4)$, total 19, at 3392879 or 3374870.
- Total19 conditional cycle: $(5,4,3,5,3)$ and its reversal $(3,5,3,4,5)$, total 20, at 3409843 and 3410730.
- Hypothetical total20 conditional cycle: $(5,4,2,5,5)$ and $(5,4,3,4,5)$, total 21, at 2978568 and 2980150.

A bounded continuation is to test these exact 012345 count cells, beginning with the completed tuple and one of the hypothetical conditional tuples. Their shared condition is middle count at most 3 and total at most 21, but there is no evidence here that this broader cell is impossible. It is only a way to identify a possible common count-sum target. Local witnesses could refute that proposed strengthening, and a checked local contradiction would still need transfer and graph integration. No new probe was run during this audit.

## Reproduction and pins

The script is `scripts/independent_cycles.py`; invoke it without an output argument to print a fresh result, or supply a new path with `--output`. Existing evidence cannot be overwritten. The saved JSON contains every full key, both placements, all nine rule evaluations, diagram routes and input hashes.

| Artifact, relative to 114 | SHA-256 |
|---|---|
| `scripts/independent_cycles.py` | `6490ddbb1eb5dc153de65e0c9e613e492af3f03f966ab4f4aad1d8ef5c83afc7` |
| `data/cycle-audit.json` | `fc245e6a30bb01b820434437bb8c20fc3c46f5d4016e7da7567618722d3e1eda` |
| `data/total19/results.json` | `f5028e214497577cd79471c266f49a36bf3455850c79b1b7d8753084e47152e7` |
| `data/total20-hypothesis/results.json` | `ae267fe66e2f6b04fd5960d253d19c6110ec586eaabcfb632e00e4a0d20d24a3` |
| `data/probes/012310-total18.json` | `8239b1a79b7ba09e0864c5e44cd9fbf5245589526bbf700818a9bf2bd0c7d6b9` |
| `data/probes/012310-total19.json` | `edefa939267f41aa24511f7c668a049a4155cd1b13949b12b4cb41bf7d5947e9` |

The read-only retrieval of the pinned Git algorithm source emitted an existing commit-graph warning, then succeeded; its resulting source hash agrees with both experiments. No inference about proof success is drawn from that warning.
