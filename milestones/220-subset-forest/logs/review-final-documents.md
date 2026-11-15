# Final source review, round 220

## Scope and conclusion

Reviewed the complete unified diff from `data/before-snake9_research.tex` to the current `paper/snake9_research.tex`, including every changed hunk, and every line 1–367 of the current `paper/snake9_frontier_explanation.tex`. The main source contains 11,113 lines. This final pass did not reread every unchanged main-source line. The preceding assigned review read all old main-source lines 4140–10979 inclusive and all old frontier-source lines 1–620; the upper main-source portion was assigned to a separate reviewer. The earlier detailed findings remain in `logs/review-construction-paper.md` and `logs/review-frontier.md`.

No substantive error was found in the revised bounds, the fixed-parent prefix deduction, the fractional feasibility conclusions, or the distinction between Lean results and native exact certificates. The parent applied the single minor notation correction identified in this review; the corrected lines were reread and the updated source hash is recorded below. No unresolved source issue remains from this pass. This reviewer edited no manuscript, compiled no document or Lean source, and ran no software tests, optimizer, or search during this final review. Source comparisons, hashes, saved receipts, and proof text were inspected directly. Typesetting and PDF inspection remain for the parent task.

## Reviewed source hashes

SHA-256 values identify the exact reviewed source state. Paths below are relative to `E:/Snake-in-a-box`.

| Source | SHA-256 |
|---|---|
| `milestones/220-subset-forest/data/before-snake9_research.tex` | `9bd201b7b4fff3a344c7785d0c36c05b4495fef386004274aaf8a7aa4b0120ba` |
| `paper/snake9_research.tex` | `0aa1a911145e7d24d4e30864bf3339ceec06ef5549771cb62226614d01892aed` |
| `milestones/220-subset-forest/data/before-snake9_frontier_explanation.tex` | `f3d42af6c27c5fe9ef67457887ab35e99d496c29c5f9ad63f78a187d1a8b8962` |
| `paper/snake9_frontier_explanation.tex` | `204ac25c4f1172ab703f1ed850944464c4055563112b916d7799ccf6d66a6eb0` |

## Resolved notation clarification

The initial reviewed version mentioned a cycle without assigning the name `C`, then used `C\setminus F` for the complement of an edge subset. The parent has corrected main-source lines 7477–7480 to name the cycle $C$ and write `\sum_{e\in E(C)\setminus F}d_e`. These corrected lines were reread. The equation label `eq:cut-parity220` is preserved, and the notation now agrees with the frontier. The odd-subset inequality and its proof are correct. The main-source hash in this report incorporates this correction.

## Bounds and logical deductions

The maintained global interval remains $191\le a(9)\le233$. Both documents identify the completed contributor theorem, its saved final assembly and axiom audit, and the pending independent full rebuild. The revised historical 235 discussion and conditional 234/share-floor material are clearly separated from the completed 233 result. The frontier's original-potential deduction is arithmetically consistent: $4720m\le1104463<1104480=4720\cdot234$ implies $m\le233$. The retained square-budget consequence $39m+2s_0\le9192$ supplies the historical 235 bound. The corrected rounding account gives $2520\cdot72/5-1008=35280=2520\cdot14$.

The new exact feasible objective values and upper certificates match `data/forest-audit.json`:

| Fixed root | Exact feasible total weight | Exact upper bound |
|---|---:|---:|
| 0 | $22588258102073/230867380070$ | $97.840921$ |
| 78 | $3545809907526/36419686519$ | $97.359759$ |

The decimal feasible values quoted in the main source are correctly rounded to six decimal places. Both exact upper bounds are below 98. For an actual odd-edge partner, the even vertex count is therefore at most 96, so its edge length is at most 95. An arbitrary admissible partner of length at least 97 would have an admissible 97-edge prefix beginning at the same fixed root. That prefix has 98 vertices and is excluded. Hence arbitrary partners at these two roots have at most 96 edges, giving $98+1+96=195$ for a one-crossing join with this particular 98-edge parent. The manuscript correctly retains the fixed-parent and fixed-root scope; it does not infer a global 195 upper bound. It also correctly leaves the 93-edge target open.

The frontier preserves the distinction between lower-dimensional constructions, source-specific normalized histories, and global bounds. Its displayed joining and component length decompositions are arithmetically consistent. The status of one exhausted six-step case and 27 unresolved cases, with four partly explored saved cases and 23 cases still at their initial state, is internally consistent. The revised discussion removes the stale announcement of direct searches already performed in round 218.

## Fractional feasibility and parity

The forest inequality is correctly derived for an induced path restricted to a vertex subset, including the empty selected subset. Under the degree identity, its boundary-plus-endpoint form follows by signed linear algebra. The sink capacities include the root endpoint and the free endpoint with the conventions stated in the preceding model.

The saved all-family claim has the appropriate scope. The exact feasible points are checked against every cycle occupancy inequality through deleted-edge potentials, and against every subset forest inequality through one feasible sink flow for each of the 158 vertices. The 832 directed arcs per flow network and 158 flow systems per root agree with the saved audit. Feasible flows suffice by summing conservation across a cut; maximum-flow optimality is unnecessary. Convex mixing with the corresponding actual one-edge path preserves all these linear inequalities and gives total selection weight exactly 94. These are fractional assignments, and neither document claims an actual 93-edge partner.

The product-disagreement expression $d_{uv}=x_u+x_v-2y_{uv}$ is correct for Boolean selections with actual edge products. The odd-subset cycle inequality follows from even disagreement parity. The root-0 square $(44,45,61,60)$ has disagreements $(0,1,0,0)$ at the saved round-220 primal point and violates the corresponding inequality by exactly one. Its exact-weight-94 mixture retains violation $21239798966440/22126523341933>0$. The independent parity audit also confirms square violations at root 78. Thus these inequalities exclude the displayed fractional witnesses while leaving the feasibility of the strengthened formulation unresolved. Both documents explicitly state that no linear program including these parity rows has been solved in this round.

The final review used the earlier independent parity audit of all 40 saved worst witnesses and all 20,512 odd-subset inequalities on the saved square and six-cycle collections. It did not repeat that computation. The historical literature attribution is consistent with the author-hosted Barahona–Mahjoub paper supplied by the parent; this final review did not independently reopen that external PDF or establish a novelty claim.

## Lean scope and receipt inspection

Read the complete current `Forest220.lean` source and inspected its successful receipt and compiler log. Its three counting theorems operate on an actual indexed induced path, distinct enumerated edges, and supplied endpoint membership. The proof charges each edge to an index away from the marked selected index. The degree-boundary theorem is a separate integer implication under the degree identity. These statements support the mathematical discussion, while concrete array interpretation and the complete numerical certificate composition remain separate.

The saved `Forest220` receipt records exit code 0 and the expected axioms: `propext` and `Quot.sound` for the three counting results, plus `Classical.choice` for `degree_boundary_iff`. The saved `SquareParity220` receipt records exit code 0 and no axioms for `boolean_disagreement`, `square_single_edge`, and `square_three_edges`. The latter module checks the two representative square forms by Boolean cases; it does not prove the arbitrary-cycle assertion. The manuscripts state this distinction correctly. The source and compiler-log hashes for both modules match their receipts. No compiler was rerun in this review.

The exact flow, upper-row, rational-point, and parity arrays have native exact audit receipts. The sources explicitly avoid claiming an end-to-end Lean check of those arrays. No independent rebuild of the full contributor 233 dependency chain was attempted, and no new claim about its reproducibility is made.

Receipt hashes, relative to the milestone directory:

| Receipt | SHA-256 |
|---|---|
| `data/Forest220-audit.json` | `d3783042fef8077362851b4e362d3729fc45357cd6ba0eff212a52d06d968bc8` |
| `data/SquareParity220-audit.json` | `464870411e01bc0f926b84f3fc85ce3698c1069c4698fab2a1b106f6d52ccccc` |
| `data/forest-audit.json` | `57ace9b15ef58fccaa716bf7c3167b39dd842c5f44f148fcc625c3e22c51ffad` |
| `data/parity-audit.json` | `62df13a4449fe21e1c12628f9b62acae3c49a94cc6b05c65d980575ecbba34f8` |

## Preservation and remaining review limits

Independently compared the source metadata and labels. All 342 original main-source labels remain in their original relative order; the revised source has 347 labels and no duplicate labels. The five additions are the two round-220 subsection labels and their three equation labels. Both original author blocks are unchanged and preserve Iori Hironaka, Tommy Ma, and Steven Zhan. The main `hypersetup` block is unchanged. The frontier had no `hypersetup` block or equation/reference labels before or after consolidation.

The revision corrects the previously undefined sum symbol, historical/current status wording, endpoint convention, and fractional-cardinality wording. The frontier now presents the upper-bound argument, construction limitations, current search state, and round-220 relaxation result in a substantially shorter sequence. This review does not reprove every archived theorem or revalidate every historical native exhaustion. The claims about those older results were reviewed for dependency scope and consistency with the stated retained evidence. Final compilation and visual review remain outstanding at this source state.
