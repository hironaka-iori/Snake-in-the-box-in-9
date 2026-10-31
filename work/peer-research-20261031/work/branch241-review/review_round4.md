# Round 4: mutual code review and exhaustive all-8-cycle cuts

The main agent reviewed my all8_cycles.py and found a real API bug: validate_cycle accepted an induced cycle shifted outside the declared Qn because its n argument had not been used to check vertex ranges. The enumeration itself constructed bounded vertices, so this did not affect the 77,868-cycle result. I fixed the validator and enumerator to require integer dimensions and integer, non-Boolean, in-range vertices. Eleven negative input tests now reject out-of-range translations, negative coordinates, floats, Boolean coordinates and invalid dimensions. The original failing template-plus-16 with n=4 is among those tests.

The fixed implementation again checks all 12,870 candidate Q4 subsets, produces exactly 168 templates, embeds them into 4,032 Q4 faces and returns 77,868 cycles inside the one-centre radius-four ball. Every returned cycle is independently checked, and all vertex sets are distinct. The complete proof, including why no cycle is missed or counted twice and the closed count 126*(168+5*84+10*3), is in all8_completeness.md.

This is a stronger search optimization than banning only the 294 cycles through the fixed three-vertex root window. The earlier root-only run demonstrates why it is needed: all 22 independently checked models in its snapshot place the centre in a 7-vertex path while retaining 110 other selected 8-cycles across the models. Root-only exclusion therefore removes a recurring local obstruction but leaves an explicit peripheral-cycle escape route.

The remaining research question is whether the complete set of valid eight-cycle cuts eliminates the low-charge query, or whether longer induced cycles remain. A finite-budget UNKNOWN result must retain its proof and be reported as unresolved. No numerical upper-bound improvement follows solely from enumerating these clauses.

## Actual all-8 run and retained proof audit

The integrated --all8 runner's static8.json.gz was compared against a fresh complete enumeration: the exact 77,868-element sets agree. Rebuilding the original objective/geometric clauses plus this static list reproduces the checkpoint CNF SHA256. The retained proof snapshot contains 5,732 learned clauses and 1,139,084 unit hints; every hint was independently replayed. There is no empty clause and no SAT model in this snapshot. Its status is therefore unresolved ACTIVE/UNKNOWN, not UNSAT.

The static cuts are part of the CNF hash and appear before the retained learned proof, so positive hint IDs retain their intended meaning when a checkpoint is reconstructed. The existing reset of learned proof after adding a new lazy geometric cut remains necessary and correct.

## Review of the proposed root-propagation optimization

It is sound to propagate at decision level zero to a complete fixed point, then rebuild watched lists while omitting clauses with a permanently true level-zero literal. Every other clause at a non-conflicting fixed point must have at least two unassigned literals; those may be placed first. Keep all original literals and clause IDs, since the independent RUP checker references that original database. If root propagation finds a conflict, preserve its clause ID and emit the proof rather than attempting normal rebuilding. A solver timeout must still not allow reuse of a partially processed trail.

## Final solver/runner implementation re-review

The implemented permanent-root watch rebuild was reviewed and independently tested with a 20-step implication chain, a contradiction reached during root propagation, and a conditional contradiction that requires learned clauses referring back through the whole root chain. All resulting UNSAT proofs passed the separate checker; the corresponding SAT case also passed its full clause check. The 2,400-case independent random regression and seven-into-six pigeonhole proof were rerun successfully after the solver change.

The optimized runner checks an already verified proof prefix once on restoration, then checks each new proof tail against the static base followed by that prefix. This is sound by transitivity of clause entailment. A targeted test splits a learned proof, independently checks prefix and tail and confirms the hint count equals a complete replay. Adding geometric cuts still resets the retained learned prefix and its accumulated verification counters.

Solver.solve's time measurement excludes the constructor's new root propagation and watch rebuild. Compare actual end-to-end wall time for performance claims; the runner's elapsed time includes construction.

## Final all-8 outcome: a checked local exclusion

After resuming with the reviewed root-watch optimization, the cap-21 query completed with UNSAT. I independently rebuilt its entire static CNF, compared its 77,868-cycle manifest against fresh exhaustive enumeration and replayed the complete retained proof from the original static base. All 7,621 RUP steps and 1,604,124 unit hints passed, including the final empty clause. This supersedes the earlier unresolved snapshot above.

Thus no necessary-condition window model with all valid eight-cycle exclusions has 21alpha+2e2+e3+V<=21. Since the score is integral, it is at least 22 on any genuine snake's internal vertex. Translation and coordinate permutations carry any induced two-edge root window to the checked one, so this pointwise statement is universal for internal roots. Its proof remains a checked computational result with the reviewed CNF soundness argument, not a Lean theorem.

This local threshold is insufficient to improve the project's current numerical upper bound. There is also a genuine bank root with score 71 (bank 44, index 83), so a much stronger pointwise threshold that alone would imply 234 is impossible. The correct numerical route remains multiple-centre window means plus the project's automaton/aggregation method. The all-eight-cycle enumeration and root-watch optimization can now be reused for those queries.
