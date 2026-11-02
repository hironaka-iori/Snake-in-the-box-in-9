# Final independent review of milestone109

No blocking error was found in the reviewed theorem statements, catalogue reduction, or finite-check scope. The reference-coverage check had completed by the time of this review. This review launched no compiler, solver, replay, or full-edge numerical calculation. It read the sources, receipts, logs, scripts, and saved results; checked artifact hashes and small arithmetic; and inspected the saved potential vectors' lengths and ranges. Only this report was written.

## Checked actual-snake statements

`ActualRelaxed109.lean` transports the milestone108 exclusion to actual nine-dimensional snakes. For a fitting six-transition window canonically equal to `[0,1,2,3,0,4]`, it proves

$$
\alpha_{r+1}\ge3\quad\text{or}\quad
\alpha_{r+4}\ge3\quad\text{or}\quad
\alpha_{r+5}\ge4.
$$

Its two edge-retention theorems use precisely the aligned count offsets 0 and 1, with reversal applied to both the direction slice and the internal centre counts. The saved graph test finds no additional accepted keys removed by this first exclusion. The theorem and the zero-hit result are different claims, each supported by its own evidence.

`NewRelaxed109.lean` checks the relaxed `01234` semantic certificate with bounds `[(0,1),(0,5),(0,21),(0,2)]`, reusing the unchanged CNF contradiction. For every actual snake and fitting five-transition window with five distinct directions, it proves

$$
\alpha_{r+1}\ge2\quad\text{or}\quad
\alpha_{r+2}\ge6\quad\text{or}\quad
\alpha_{r+4}\ge3.
$$

The only hypotheses of this actual-count theorem are the snake, the fitting inequality $r+5\le m$, and the canonical direction pattern. There is no remaining reference-catalogue or unproved count-floor premise in this local result. The argument correctly bounds the unconstrained third count by 21. The two edge-retention statements use offsets 0, 1, and 2 and the existing interval-exclusion lemmas, preserving the reverse-count alignment. A symbol 6 continues to represent the interval `[6,21]`.

The actual-snake conclusions concern these local windows. They do not establish the longest possible snake or certify the full modified graph.

## Twelve closed reference entries

`ReferenceCoverage109.lean` passed in the saved run. It combines the earlier eight keys with indices 1006, 1010, 1011, and 1014. Their symbol lists under directions `[0,1,2,3,4]` are `[1,5,4,2]`, `[1,5,5,1]`, `[1,5,5,2]`, and `[1,5,6,2]`. Each interval list is contained in the proved relaxed bounds. The generic centre-weakening direction and the full-list filter equivalence are unchanged from the reviewed milestone108 proofs.

The final filter theorem establishes equivalence of the full 1,378-key obligation with the list excluding these twelve proved keys. Its checked length is **1,366**. The remaining keys are still explicit obligations; the summary correctly records `full_reference_union_checked: false`.

## Receipt verification

All nine receipt hashes in the final proof summary match the current receipt files. For each of the three wrapper modules, the current source, preserved source snapshot, compiled object, and successful log match the receipt hashes. All three runs exited with code 0 and no timeout. Their 3, 8, and 3 printed axiom reports total 14 and contain only `propext`, `Classical.choice`, and `Quot.sound`, with smaller sets for some individual statements.

| Module | Checked time | Receipt SHA-256 |
|---|---:|---|
| `ActualRelaxed109` | 10.046 s | `8489073d2e62b133ae9cc53c24fbd8cb7ff458217893df8d885cbbf7d8d4f332` |
| `NewRelaxed109` | 46.390 s | `002c9249e064b0250dd002c9fcc7a3197ad8f269d17789140cba0ae229f2c427` |
| `ReferenceCoverage109` | 15.234 s | `fd547077fac6f4b47cbf308d50dd092a3e63436d637ad913d70d203c63ee2bc8` |

The reviewed final `data/proof-summary.json` hash is `1cb843efd7542e96e77c320a2d9bb5b00886bd9bca3c2d1aa2e99d3aff995471`. This is verification of the saved local evidence, not a clean rebuild of the inherited dependency closure.

## Restricted finite graph

`evaluate_restriction.py` uses the proved `01234` rule with the correct three offsets and both orientations. Its removed full-key hash agrees with the earlier candidate screen. It preserves the original state numbering and graph weights, selecting the surviving edges by the full key rather than merging endpoint pairs. The saved result removes 2,092 of 4,947,008 edges, leaving **4,944,916**.

For each profile, the script constructs integer potentials by relaxation, requires convergence, and checks every remaining edge inequality. It separately checks that an old cycle survives, is closed under the saved endpoints, and has mean equal to the proposed value. Those two checks establish the reported finite minimum cycle mean. The evidence is a native integer calculation with saved hashes, not a new Lean certificate for all restricted edges.

| Profile | Finite minimum cycle mean | Displayed potential range | Comparison value |
|---|---:|---:|---|
| Completed local floors | 483 | 551 | $157625/669$, integer part 235 |
| Conditional floor-18 profile | 496 | 602 | $551765/2348$, integer part 234 |

I independently verified that both saved potential vectors contain 1,601,856 entries, have the recorded decompressed hashes, have minimum 0 and the listed maxima, and satisfy the reported comparison arithmetic. I did not re-evaluate all edge inequalities. The script's fixed-point assertions and preserved sharp cycles support its exact finite conclusion; the displayed ranges are the ranges of the saved potentials. No claim of a new range-optimality theorem is required.

The restricted graph has no new complete Lean graph certificate or assembly in this milestone. The conditional profile retains its existing floor assumptions. Both numerical comparisons are unchanged, and neither is presented as a newly closed global snake bound.

## Surviving obstructions

`check_obstructions.py` uses the same count and direction alignment for all candidate tests. It checks saved path chaining, surviving edge indices, recomputed path weights under each tested lowered floor, and a surviving cycle of mean 496. Its five recorded ceilings are 111960, 111959, 111960, 111960, and 111960 for cases 7301, 7302, 7303, 7307, and 7308 respectively. I independently checked the arithmetic identity

$$
\mathrm{ceiling}=(227-L)496+W
$$

from each saved path length $L$ and weight $W$. The script has $L\le227$ and every ceiling is at most 111960. A surviving mean-496 cycle forces an admissible potential slope $P\le496$, while the path forces $R\ge LP-W$. These facts obstruct the strict comparison needed for integer bound 234 when the specified floor is lowered by one and the other current floors are fixed. This is an obstruction within the fixed finite model and charge-potential method. It does not prove that the local mathematical floor itself is necessary or optimal for actual snakes.

All 16 screened proposed relaxations have empty hit lists on both saved critical cycles. This is a finite observation for the screened proposals and eligible graph placements. It makes no claim about unscreened sources or different exclusions. Apart from the two already proved rules, candidate relaxations remain hypothetical.

The reviewed scripts' hashes and all lightweight pinned inputs of the two result files match. The large NPZ input was not rehashed or reprocessed in this final review. Result hashes are:

- `restricted-profiles.json`: `b38036cb72850309d8310dd173b79b040164461e2238ad0da73693270a7ad7eb`.
- `obstruction-survival.json`: `e86fdd9922b9e0b3f9cbcaf41706e9042b4f0cd1969454d52f4cff7364a56ddb`.

## Highest-value continuation

Broaden the archived-source `.over` dependency screen and prioritize candidates that hit an edge of the actual critical cycles. Preserve the exact direction/history/count key, eligible offset, reversal, and symbol-6 interpretation when scoring such hits. A proposed counter relaxation must still receive its semantic kernel check before its hits justify removing any edge.

Raw removed-edge counts are a poor priority here: 2,092 deletions left both means and displayed ranges unchanged. More decisively, even the ideal range $R=0$ at the surviving means gives

$$
\frac{1098960+8\cdot483}{4200+483}=\frac{367608}{1561},
\qquad
\frac{1098960+8\cdot496}{4200+496}=\frac{137866}{587},
$$

whose integer parts remain 235 and 234. With this same charge comparison, range reduction alone cannot improve either integer bound while these mean constraints remain. Since all 16 current candidates miss both displayed critical cycles, combining those same proposed deletions would still preserve these cycle obstructions. Screening a broader source set for critical-cycle hits is therefore the most direct next test. A cycle hit is necessary for this route to improve the slope, but is not sufficient: other critical cycles may remain, and the resulting graph still needs its potential and retention checks.

## Addendum: checked comparison barriers

`RangeBarrier109.lean` subsequently passed its saved Lean run in 6.484 seconds. This extends the reviewed collection from the historical nine-module, fourteen-report phase above to **ten checked modules and sixteen axiom reports**. The proof-summary hash quoted earlier identifies that earlier phase; this addendum independently pins the additional module's receipt.

The new theorems state, for integers $P,R$,

$$
P\le483,\quad R\ge0
\quad\Longrightarrow\quad
(4200+P)235\le1098960+8P+R,
$$

and

$$
P\le496,\quad R\ge0
\quad\Longrightarrow\quad
(4200+P)234\le1098960+8P+R.
$$

The inequality directions and constants agree with the stated comparison barriers. With the usual positive denominator $4200+P$, they prevent this quotient comparison from giving a bound below 235 or 234 respectively. The Lean statements themselves use cross-multiplied integer inequalities and require only their displayed slope and nonnegative-range hypotheses. They introduce no new definitions and assert no additional fact about graph cycles, actual snakes, or the completeness of the remaining reference catalogue. Establishing the applicable slope ceiling remains separate from these arithmetic theorems.

The current source, saved source snapshot, compiled object, and successful log all match the additional receipt. Both printed theorem audits use only `propext` and `Quot.sound`. No compiler was run by this reviewer.

| Additional artifact | SHA-256 |
|---|---|
| `lean/RangeBarrier109.lean` | `31a70f846f581d38d4fa4fc0ad8962dc9faf268fbc369a5a0a9df22aa52ff86d` |
| `data/RangeBarrier109-audit.json` | `1f9541eb23f2ea93512429232a20b63ae4e84fac2b0bb454f8801bfaffcc3b04` |
| `build-isolated/RangeBarrier109.olean` | `28b340422155b806bed4736bbdd3caf6462a4f37746e56b9ac042206000e7c2e` |
| Successful log `RangeBarrier109-1793653928541661600.log` | `bfc6160829265e0a344f7f6b445b6d1e542a3b36f7481fded8bffe3ba67bf57d` |
