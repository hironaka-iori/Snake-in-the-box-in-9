# Milestone 57: share candidates covering the replacement family

This continues the empty-square route. The contributor-checked global interval remains **191 <= a(9) <= 235**. This round improves an exploratory finite model; it does not establish a new global bound.

## Coverage before proof replay

The full minimum-charge family in milestone 55's model consists of one component with 37 states, 48 transitions and 17 five-centre patterns up to reversal. Every critical transition has zero recorded share credit. Nine individual patterns each meet every cycle in that component. These were selected for screening before attempting further certificate replay.

Ordinary controls on those nine patterns give seven verified local forests and two numerical exclusions. Share-cap-95 tests on the seven feasible ordinary cases give three numerical INFEASIBLE results and four UNKNOWN results. The other eight patterns were not screened this round. UNKNOWN provides no exclusion.

The three proposed share-96 rows are listed below. Distinct letters denote distinct coordinate labels, and A and B lie in [6,21]. Counts are the five internal singleton-square counts.

| Directions | Counts | Ordinary local share |
| --- | --- | ---: |
| (a,b,c,d,b,e) | (5,2,A,3,B) | 297 |
| (a,b,c,a,d,b) | (A,2,5,2,B) | 302 |
| (a,b,c,d,b,e) | (2,5,2,A,B) | 534 |

These are **numerical candidate inequalities**, with no Lean refutation replay yet. The local forests prove consistency of the ordinary conditions only; extension to complete snakes is unresolved.

## Exact finite-model comparison

The first candidate, applied in both orientations, strengthens the charge while leaving all ordinary transitions unchanged. The model's exact normalized minimum rises from 102/25 to **49/12**. Adding all three candidates gives the same minimum. Both comparisons have all-edge integer-potential checks and attaining twelve-step cycles.

Each model has 3,042,328 transitions, integer weight mean 490 and potential range 650. The resulting conditional edge estimate is 110388/469, whose integer part remains 235. The inherited numerical exclusions and the new candidate shares remain explicit premises. A full graph-to-snake Lean assembly has not been completed.

The replacement twelve-step cycles have zero recorded share credit, including in the combined model. Thus replaying the other two candidates would not improve this model's mean beyond the effect of the first. The next discovery target is the replacement family at mean 49/12, seeking a further valid share rule with enough combined effect to cross the 234 threshold. The current candidates can be replayed once a sufficient set of premises has been selected; none is represented as proved here.

## Checked rank certificate and independent checks

Deleting the five edges carrying the first candidate's pattern makes the recorded 48-edge critical graph acyclic. A rank strictly increases along every remaining edge. Lean checks the finite rank certificate, the edge implication, the path summation, and the conclusion that every nonempty closed walk uses that pattern. Its four dependency audits contain only standard axioms, with no axioms needed for the finite rank-table check. This theorem concerns coverage of the recorded graph; it does not prove the candidate share lower bound.

The independent verifier checks all source graph hashes, nonnegative potential slack on every transition, the complete critical component, all nine single-pattern covers by a separate acyclicity test, seven ordinary local forests, both updated share arrays, both full potential inequalities, and both attaining cycles. See `data/verification.json`.

## Files and continuation

- `scripts/critical.py`, `prioritize.py`: extract the complete critical family and prioritize patterns that individually meet all its cycles.
- `scripts/probe.py`: ordinary controls followed by share-cap tests for those nine patterns.
- `scripts/apply_candidate.py`, with optional `--all`: reproduce the single-candidate and combined numerical models.
- `scripts/prepare_rank.py`, `check_lean.py`: generate and check the finite coverage proof.
- `scripts/verify.py`: independent finite and geometric verification.
- `candidate/` and `combined/`: exact finite-model evidence, with generated arrays excluded from Git.

This is research round 1 of 10 after manuscript revision 56. The paper and editor mirror remain at the synchronized 235 revision, with unchanged authors and hyperlink settings. The next scheduled paper revision is milestone 66. The compiler limitation recorded in milestone 56 remains unresolved.
