# Round 220 review of the frontier explanation

## Scope

Read all lines 1–620 inclusive of `data/before-snake9_frontier_explanation.tex`, in ranges 1–250, 251–500 and 501–620. This includes the title, all three authors, the round-219 date, all mathematical discussion and the complete bibliography. Also read manuscript lines 4140–10979 for comparison. No source edits, tests, solver runs, certificate replays, external-source verification or rendered-layout inspection were performed.

The source supports the stated maintained interval \(191\le a(9)\le233\) at the saved contributor-theorem evidence level, with a fresh independent full rebuild still pending. The exact degree-and-cycle assignments are fractional feasible points, with no new path construction.

## Recommended changes

1. **Limit the dimensional claim to its witness, lines 205–209.** The 52-vertex face proves that the specified 98-edge representative cannot have that face supplied by a single 51-vertex parent. The sentence “passing to higher dimension requires compatible collections of paths” reads more broadly than this evidence. Replace it with: “This representative therefore requires retaining several path components in that face.” The precise deletion-only obstruction at 234–239 can then supply the broader explanation without implying that every higher-dimensional construction needs disconnected faces.

2. **Remove the stale direct-search announcement, lines 523–529.** The degree-and-cycle search announced there is reported at 534–549. Replace the future sentence with a cross-reference to the ensuing model and its two UNKNOWN outcomes. Keep the 97-edge exclusions explicitly restricted to the saved parent and without Lean contradiction certificates.

3. **Update the round-220 boundary only from the completed result, lines 578–585, date line 13, and lines 604–605.** The subset-forest inequality is justified for integral path assignments. At the saved round-219 cutoff its effect is unknown. When the new calculation is complete, replace the future sentence with its actual outcome and verification scope. Do not infer a lower bound, an integral exclusion, or a global upper bound from a fractional calculation.

4. **Consolidate the current status in the “current construction frontier,” lines 280–585.** The section has become a round-by-round account. In particular, the region counts at 365–368, 411–414, 465–469, 481–482, 511 and 531 concern successive cutoffs or different retained pairs. Give one opening status paragraph: one exhausted six-coordinate case, 27 unresolved choices, four saved open cases, and the latest recorded count for the actively continued case. Retain earlier node and operation counts only where they illustrate a mathematical point, or move them to the companion manuscript/record. This would make the document's “short explanation” title more accurate.

5. **Consolidate the checked-versus-pending account, lines 386–446 and 449–479.** The earlier paragraph says the geometric assembly is separate, then the later paragraph explains the source-specific connection completed in round 213, followed by parity membership in round 214. State the strongest current connection once, and keep the remaining obligations explicit: current domain fitting, concrete table and normalization interpretation where applicable, and complete native traversal. The earlier statements are historically qualified but unnecessarily difficult to reconcile in an explanatory document.

6. **Define notation at first use.** At line 284, state that \(d\) is Hamming distance. In the subset-forest paragraph 578–580, define \(x_u\) as vertex-selection weight, \(y_{ab}\) as the induced-edge variable, and \(E(U)\) as allowed edges with both endpoints in \(U\). The current prose introduces edge variables generically at 554–555 but does not assign the symbols used in the final inequality. Explain the unselected-anchor case in one clause if the inequality remains: when \(x_v=0\), the weaker forest bound still holds.

7. **Describe the decimal lower bounds accurately, lines 556–561.** The printed values 98.044957 and 97.654360 are outward-rounded lower bounds derived from the exact rational assignments printed in the manuscript. Say “The lower bounds are obtained from saved rational assignments” in place of “Both lower endpoints come from saved rational assignments,” or supply the exact fractions. The current text should not imply that the rounded decimal endpoints are themselves the archived assignment cardinalities.

8. **Reduce superseded upper-bound detail in the short document, lines 129–179.** The completed B233 deduction at 113–127 is concise and useful. The alternative 234 and relaxed 233 calculations are correctly qualified, but occupy substantial space despite yielding no better maintained interval. Retain a compact explanation of their separate premises and send detailed floor profiles and allowances to the companion manuscript. Preserve the exact B233 arithmetic and independent-rebuild qualification.

## Mathematical inspection

The square identity, empty-square share accounting, B233 arithmetic, two-parent crossing identity, slice criterion, coordinate-history pair condition, square-base capacity, tight-subset reasoning, continuation coverage and fractional-cycle telescoping are coherent under their written assumptions. The all-cycle feasibility claim is clearly restricted to the continuous model at 568–576. The final paragraph correctly separates a new parent from a compatible construction and states that proving optimum 196 needs both a witness and a universal 197-edge exclusion.

This review does not independently establish the contributor theorem, verify its imported objects, check each saved native search, recompute the rational arrays or validate the printed witness lists. Those proof and data boundaries must remain visible after revision.

Only this log and `logs/review-construction-paper.md` are written. The three authors remain unchanged, and no document metadata is edited.
