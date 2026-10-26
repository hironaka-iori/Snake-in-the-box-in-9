# Milestone 55: share constraints across the critical family

Verification complete: 102 Lean modules and 10 dependency audits pass; see `data/verification.json`. The selected route remains empty-square charging. The candidate local theorem is:

For six consecutive directions (a,b,c,d,a,e), with the five named coordinates distinct, suppose the five internal singleton counts are (A,B,2,2,C), where 6<=A,B,C<=21. Then their resolution-12 integer shares sum to at least 96.

The ordinary radius-four model has an independently checked forest witness with share 450. The native share-cap-95 refutation passes independent DRAT verification. It has 11,751 core clauses, 7,218 active variables, and 1,063,501 replay hints. The original formula has 444,845 clauses; four independent semantic assignments, including the matching forest and three complete bank snakes, satisfy all clauses except the explicitly mismatched count or cap premises. The matching forest fails exactly the share-cap clause. The lower bound is not asserted to be sharp, and the local forest is not asserted to extend to a complete snake.

## Selecting one inequality for an entire critical family

Milestone 54's strongest exploratory model has exact minimum normalized charge 53/13. All transitions on minimum-mean cycles lie in one strongly connected component with 57 states and 83 edges. There are 26 distinct five-centre windows up to reversal; every critical edge has zero credited share under the previous rules.

Twenty-five of these windows have independently verified ordinary local forest witnesses. Share-cap-95 screening gives nine INFEASIBLE results and sixteen UNKNOWN results. The remaining ordinary window is UNSAT and receives no share test. UNKNOWN is not an exclusion. Only the selected pattern is sent for certificate replay in this round.

A single proposed inequality, the pattern (a,b,c,d,a,e) with counts (A,B,2,2,C), meets every cycle in the recorded critical component. It occurs on four of the 83 edges. Deleting these four edges leaves an acyclic graph. The rank certificate is written in `lean/CriticalShareCover.lean`: every edge with a different label strictly increases an integer rank, so every nonempty closed walk must use the selected label. This concerns the recorded finite graph; identifying all actual snake windows with the full model remains a separate proof obligation.

The minimum-cardinality claim is also independently checked: one selected pattern covers the component, while the original component contains an explicit cycle and therefore cannot be covered by zero patterns. The numerical ordinary exclusion found during controls also removes all current critical cycles. It is retained as a separate comparison, without starting an ordinary-exclusion search.

## Effect on the complete model

Adding the selected share bound in both orientations raises the exact exploratory mean from 53/13 to 102/25. A replacement 25-step cycle attains the new mean, and an integer potential verifies it on every allowed transition. The ordinary-control comparison reaches the same mean.

| Additional premise | Allowed transitions | Normalized mean | Scaled potential range |
| --- | ---: | ---: | ---: |
| Selected share bound in both orientations | 3,042,328 | 102/25 | 3,216 |
| Ordinary exclusion found during controls | 3,042,286 | 102/25 | 3,216 |

Both models give the conditional edge estimate 229973/977, whose integer part is 235. The numerical rules inherited from milestone 54 are still premises of these models. A successful local Lean replay does not certify those inherited rules or complete the global graph-to-snake proof.

The coverage calculation proves that the selected local inequality affects every previously minimizing cycle. It does not prove that those cycles occur in a complete snake, or that all replacement cycles have enough charge for 234. The next mathematical target is the new minimum-charge family, with priority given to inequalities that affect the entire family.

## Evidence and reproduction

`scripts/critical.py` extracts the critical component from an exact potential. `scripts/cover.py` solves the finite cycle-cover problem and checks minimal cardinality independently. `scripts/verify_finite.py` independently checks the critical component by reachability and acyclicity of its complement, all positive controls, the full transition changes, and both potential/cycle certificates. `scripts/verify.py` additionally checks certificate identity, the complete Lean build, and dependency audits.

`scripts/replay.py --resume` preserves successful source-matching modules in the pinned local Lean environment. Raw certificates can be restored with `scripts/archive.py --unpack`. The compressed certificates and their hashes are retained; build products are ignored by Git. The current source inventory includes an explicit reversed-snake application of the selected local theorem.

This is research round 9 of 10 after manuscript revision 46. The contributor-checked global interval remains 191<=a(9)<=235, and the full contributor dependency closure has not been rebuilt locally. The paper and editor mirror remain unchanged; the scheduled manuscript rewrite is at milestone 56.
