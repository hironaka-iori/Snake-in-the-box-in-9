# Independent review of the outer-three graph exclusion

The bounded saved-cycle audit passes. The new exclusion removes63 full keys across51 direction/history contexts, leaving4697760 edges on1601856 states. Every newly removed key was independently checked against the exclusion. Both graph profiles retain their previous mean, potential range and comparison:

| Profile | Replacement cycle length | Mean | Potential range | Comparison | Integer part |
| --- | ---: | --- | --- | --- | ---: |
| Completed | 18 | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional floor18 | 5 | $496$ | $602$ | $551765/2348$ | 234 |

The previous completed cycle survives. The previous conditional three-cycle loses edge18806 at placement1 and edge1130461 at placement0. Its remaining edge does not complete the old cycle. The replacement five-cycle has zero bonus from all thirteen inherited sum rules and avoids the new exclusion at both placements.

## Exclusion and orientation

The producer matches the six-transition shape $012031$ up to coordinate relabelling and reversal, and rejects an edge when the four outer count symbols at positions $s,s+1,s+3,s+4$ are at most3, for either placement $s=0$ or $s=1$. The middle symbol is unrestricted. These four positions and their common cap are symmetric under reversal, so the predicate is unchanged when the five count symbols are reversed. The independent audit includes200 guard-reversal checks, as well as the2180 checks for the inherited asymmetric rules.

For actual count intervals, each outer symbol at most3 is an exact count at most3. Middle symbol6 retains $[6,21]$ and is not specialized to6. This matches the bounds $[(0,3),(0,3),(0,21),(0,3),(0,3)]$ of the intended local theorem. Both placements are used for deletion. No additional credit is assigned by this exclusion.

The producer asserts exact reproduction of the complete milestone117 and119 removal sets and both corresponding weight-vector hashes before adding the guard. Those assertions and their source pins were inspected; the full vectors were not recomputed here. The new removed set is exactly the old set plus63 keys. The independent script checks each of those63 keys directly, although it does not scan all retained keys again to prove that no additional guard hit was omitted. That coverage remains supported by the pinned producer computation.

## Saved numerical evidence

For each saved cycle, the audit checks the full direction/history/count key against the original arrays, acceptance by the retained diagram, source and target reconstruction, original weights, floor corrections, all thirteen sum-rule tests and the new guard at both placements. It verifies chaining, retained-edge membership, potential-file hashes and dimensions, minimum zero, range, and equality in every cycle-edge potential inequality. Exact rational mean and comparison calculations agree with the producer's result.

Both saved cycles have zero deficits under all inherited rules. They therefore remain coefficient-independent ceilings for this fixed thirteen-rule family together with the new deletion guard. The balanced coefficient24 computation attains their means according to the producer's all-edge inequalities. No full-edge inequality scan or graph optimization was repeated in this review.

There is no shared canonical five-centre direction shape between the replacement cycles. The completed cycle uses $012034$, $012301$, $012304$ and $012310$. The conditional cycle uses $012031$, $012032$ and $012314$.

The conditional five-cycle has the following full keys; every history value is0:

| Edge | Direction index | Nine directions | Six count symbols | Weight |
| ---: | ---: | --- | --- | ---: |
| 2511 | 0 | $012031041$ | $(4,4,3,5,4,4)$ | 496 |
| 1101529 | 103 | $012302401$ | $(4,3,5,4,4,4)$ | 496 |
| 2186371 | 205 | $012314301$ | $(3,5,4,4,4,3)$ | 376 |
| 121059 | 19 | $012032402$ | $(5,4,4,4,3,5)$ | 616 |
| 2140357 | 198 | $012314210$ | $(4,4,4,3,5,4)$ | 496 |

Its distinct five-count windows are $012032$ with $(4,3,5,4,4)$; $012314$ with $(4,4,3,5,4)$ or $(3,5,4,4,4)$; and $012031$ with $(5,4,4,4,3)$ or $(5,3,4,4,4)$. All symbols in this replacement cycle are below6. These are graph contexts, not established actual-snake realizations.

## Reference candidates and proof status

A separate bounded scan of all1378 reference literals found exactly three entries whose intervals are contained in the new exclusion:

| Union index | Direction word | Count symbols |
| ---: | --- | --- |
| 126 | $012031$ | $(2,3,6,3,2)$ |
| 127 | $012031$ | $(2,3,6,3,3)$ |
| 138 | $012031$ | $(3,3,6,3,2)$ |

The scan checked both orientations and longer keys containing a six-transition window. All three matches have exactly six directions; no longer-key candidates were found. None overlaps the twelve entries already discharged by `ReferenceCoverage109.lean`. Its successful receipt and source hash were checked when establishing that comparison. These three entries are only candidates: no checked weakening or catalogue instantiation was performed, and the saved remaining-reference count is not changed.

At final review, `data/ActualOuter120-audit.json` was still absent. The prepared source therefore remains pending compilation in this report. Its final intended theorem has no local-contradiction premise, but this alone is not evidence of successful compilation. The native probe status and grouped proof generation must remain distinct from a completed actual-snake theorem. Even after that theorem passes, the inherited sum hypotheses and complete graph integration retain their separate outstanding obligations. No new actual-snake upper bound is claimed.

## Pins and limits

- `data/outer3/results.json`: `c60809a238d091b1a29030237860a984d28074b181fd857b1cf96c706bff2034`.
- `scripts/evaluate_guard.py`: `98ce1f517f021898ebcaf5dfd97b23715df2fbc3707644fa9b640d6f648dd824`.
- `scripts/independent_graph.py`: `9da9d2aae13fa1fedbaf5d9f7c0b406fc063f7dfc976300178a208e1b507a413`.
- `data/graph-audit.json`: `ae4ad8cc282fec444f4e69f01bd9c35b892079a79dca4d4995e170facd5c172f`.
- `data/reference-coverage-candidates.json`: `4a1639cdd32891b51c6e81dedc17d9ccd36283a1ae03443acb2c9d465e8d90a3`.

No substantive orientation or saved-cycle inconsistency was found. One source-adaptation syntax error was caught before the audit script was written or executed; the saved script passed its syntax and data checks. No solver, Lean compiler, full graph computation or Git command was run. Only the owned script, audit JSON, candidate JSON and report were written; the live proof source and checker were not changed.
