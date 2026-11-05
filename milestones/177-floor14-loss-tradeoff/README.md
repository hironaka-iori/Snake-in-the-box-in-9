# Round 177: share-floor and loss tradeoff

This round is complete. Research pauses at the user's request. No unconditional numerical bound or longer construction is added. The maintained interval remains 191–235 edges, retaining the qualification that the contributor's 235 proof has not been independently rebuilt in full.

## New result

The previously scanned potentials can be reused after weakening the pending floors:

| Pending floors (012034, 012301, 012340, 012345) | Scaled mean / scale | Scaled range | Conditional inequality | Sufficient loss for 234 |
| --- | --- | --- | --- | --- |
| 14, 14, 14, 14 | 4444 / 9 | 5384 | 42244m + 45L <= 9928336 | L >= 23 |
| 14, 16, 16, 16 | 4445 / 9 | 5374 | 42245m + 45L <= 9928334 | L >= 17 |

The completed floors and count-conditioned 012032 increment stay fixed. Decreasing a pending floor by one decreases each edge weight by at most one, including where a fixed source bound takes precedence. The old potential consequently satisfies the new edge inequalities after decreasing its scaled mean by nine. Its range does not change. Combining the telescoped inequality with the actual boundary and loss budget gives the displayed results. At m = 235 they require respectively L <= 22 and L <= 16. These cutoffs are exact for the reused scalar comparisons; their optimality over other potentials is unresolved.

This separates the local proof task by loss: if uniform floor14 and the retained graph premises are established, uniform floor15 is needed only in the hypothetical 235-edge case with L <= 22. Such a snake dominates the cube, by the established fact that an undominated vertex contributes at least 96 to L. The low-loss case is not excluded.

## Evidence and limits

`lean/LossTradeoff177.lean` passed Lean 4.19 with eight printed theorem dependency reports. It checks the maximum-weight perturbation, edge transfer, both comparisons and upper-bound implications, exact scalar cutoffs, and a criterion for a possible improved potential. The actual-snake boundary and physical budget are reused from round175. This round does not add a new combined actual-snake Lean wrapper or a complete Lean edge certificate. The finite potentials are the accepted round176 archives; their records and archive hashes are pinned in `data/completion.json`. No new full graph scan was performed.

The attempted fresh floor14 optimization did not start: 1,217,253,376 free bytes were below the established 2 GiB startup requirement. The prepared producer and guardian remain saved, with their status recorded explicitly. No child graph worker was launched. This is no evidence against the candidate potential.

For the profile (14,16,16,16), a potential at scaled mean 4448 and scaled range R would give 234 whenever R + 1 <= 5296 + 45L. Thus R <= 5340 would make L >= 1 sufficient. The archived walk forces R >= 5310 at that mean; it supplies a lower bound on the range, not a feasible potential. Existence in the interval 5310–5340 is unresolved. The prepared producer uses a generous range cap and records the actual minimum integer loss sufficient for any successful result.

All inherited local-floor, count, reference-exclusion and graph-to-snake premises remain. In particular, retain the hypothetical 0123104 six-count floor25 with its specified first-count restriction; do not treat it as a universal theorem. The separate share18 replay remains 33,111 / 145,215 deductions, without a final contradiction.

## Saved handoff

The main paper and short explanation incorporate the tradeoff in their existing files. The author order and hyperlink settings are preserved. Compilation status is in `data/latex-compile.json`. The next scheduled manuscript-wide revision remains 186; round177 is a focused mathematical addition.

Upon a user-authorized resume, first choose between completing the weaker local certificates and computing the optimal floor14 loss tradeoff. No further round should start while the goal is paused. The strongest loss-free conditional profile remains (15,15,15,15), with mean4453/9 and range5384/9. The independent empty-square target remains fourteen empty squares in a hypothetical 235-edge snake.
