# Milestone 53: empty-square shares on a satisfiable obstruction

Two new local empty-square inequalities are checked in Lean, including their application to actual snakes with arbitrary coordinate labels. The complete local build contains 203 modules; all 19 printed theorem-dependency audits contain only standard Lean axioms. The verification receipt is `data/verification.json`.

This continues route 1. The target is the contributor's sixteen-step count obstruction of mean 65/16, pinned at `74ca83db9c218446211d4f24c5e5a07329fdd847`. It avoids the previously used three-square bonus. All nine of its distinct five-centre count windows have independently verified ordinary local forest witnesses. Thus the new inequalities supply information that these ordinary count constraints do not exclude.

For six consecutive transition directions, the following rows force the sum of the five internal integer shares at resolution 12 to be at least 96. Distinct letters denote distinct coordinates, and A and B lie between 6 and 21.

| Directions | Internal singleton counts | Share lower bound |
| --- | --- | --- |
| (a,b,c,a,d,e) | (A,3,B,3,3) | 96 |
| (a,b,c,d,e,f) | (4,A,2,3,B) | 96 |

The Lean statements are in `lean/ShareInSnake0.lean` and `lean/ShareInSnake5.lean`. Their two proof certificates have 14,471 and 11,582 core clauses and 1,245,746 and 716,736 replayed hints. Each original formula has 445,111 clauses. Eight independent assignment checks exercise the complete formulas, including positive controls and recorded snake witnesses. The ordinary local witnesses for the two selected patterns have shares 378 and 855; neither establishes the minimum or extension to a full snake.

On the saved sixteen-step obstruction, the forward occurrences ending at phases 1 and 10 occupy disjoint sets of five centres: {13,14,15,0,1} and {6,7,8,9,10}. Their cyclic share contribution is at least 192. Consequently the normalized charge for this repeating pattern increases from 65/16 to

\[
\frac{24\cdot65+192}{24\cdot16}=\frac{73}{16}.
\]

`lean/ObstructionPacking.lean` checks this accounting under the two share premises. The saved direction/count reconstruction and forward orientation are independently verified by `scripts/audit_obstruction.py`. No reversal theorem is needed for the selected occurrences.

For p consecutive complete blocks, the cross-boundary occurrence is available only between adjacent blocks. The resulting lower bound is 96(2p-1), with one lost window at the boundary. `lean/FiniteBlockBudget.lean` proves the summation lemma and its conditional consequences. Under the additional actual-run count premise T >= v + 49p + 6 and the global charge budget, it yields

\[
864v+1368p\le221088.
\]

At v=236 this excludes p>=13 under those premises. The full mapping from a snake run to these block/count premises is still missing; this is not an unconditional run exclusion.

The numerical screen found four infeasible share-cap cases, one feasible case, and four timeouts. Only the two rows displayed above have completed Lean replay in this milestone. The feasible case has independently verified share 87, so a uniform lower bound of 96 for all nine local patterns is false. The additional native certificate for row 1 is preserved without a claim of Lean verification.

The contributor-checked global interval remains 191 <= a(9) <= 235. Improving one obstruction does not establish a new minimum across every allowed cycle. The next task is to insert these verified share constraints into the surviving finite models, account for overlapping windows, and identify the cycles that still avoid sufficient charge.

Research round 7 of 10 after manuscript revision 46. The next scheduled manuscript rewrite remains milestone 56; the paper and editor mirror are unchanged.

Reproduction: `scripts/verify.py` checks the saved certificates, build coverage, controls and cycle accounting. `scripts/archive.py --unpack` restores raw certificate files. `scripts/replay.py --resume` retains source-matching successful Lean modules and rebuilds missing or changed dependents. Runtime and support-library paths are the pinned local Windows environment recorded in the replay script.
