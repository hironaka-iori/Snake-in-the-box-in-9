# Round 221 final document review

## Reviewed versions and scope

- Main editor source: `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`, 11,213 lines, SHA256 `d360607a0cb3ee9fe9f83dfa9a7dfeafae8a276b6d290e5d946c1597cb6d923d`.
- Short editor source: `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex`, 390 lines, SHA256 `1ac0ebc51051f3c91c2a871abaea4c5979c96b9197b93f64828856fed81c2d56`.
- Both `E:/Snake-in-a-box/paper/` mirrors have exactly the corresponding editor hash.

Read the complete short source, lines 1–390, including preamble and bibliography. Compared both sources with `data/before-*.tex`. Read the main abstract and opening notation, the full new subsection `sec:parity221` (lines 7511–7600), its preceding product-consistency transition, the changed verification-status passage and bibliography entry. Also read the actual odd-edge model in `sec:linear219` and preceding endpoint discussion to check the prefix argument. This is a bounded revision review, not a new full reading of all 11,213 main-source lines.

Read the complete fourteen-entry `first-summary.json`, the first-step audit coverage/status, `long-summary.json`, the scope and decisive summary fields of `long-primal-audit.json`, and `flow-long-summary.json`. No numerical vectors, potentials or flows were recalculated. Their independent exact arithmetic acceptance is supplied by the separate saved audits. No compiler, optimizer, solver, software tests or manuscript edits were performed.

The complete pre-date preambles match their snapshots byte-for-byte as decoded text. Thus the three authors, author order, main `hypersetup` and all other pre-date settings are preserved. Every previous `label` remains present in both documents. Changes are confined to the intended date, result/status discussion, new subsection and bibliography entry.

## Mathematical findings

No blocking mathematical inconsistency was found in the reviewed revision.

1. **The 193-edge ceiling uses a valid prefix deduction.** A 95-edge partner has 96 vertices, starts at an even fixed root, ends at an odd vertex and has equal parity-class totals. It therefore satisfies the odd-edge model described in `sec:linear219`. The exact upper certificates 95.955197 and 95.763979 are strictly below 96. Every longer compatible partner retains compatibility and its starting root when restricted to its first 95 edges; the other endpoint is free, so no prescribed endpoint is lost. Consequently partners have at most 94 edges, and the one-crossing construction has at most `98+94+1=193`. This does not exclude a 94-edge partner, prove that 193 is attained, or bound other parents or arrangements. The proposition, abstract and short explanation preserve these restrictions.

2. **The 93-edge target and weight-94 fractional statements are consistent.** The target requires 94 vertices. Both displayed exact rational points have larger total weight. Weight `92/(q-2)` on such a point and the remaining weight on the two-vertex path gives total weight 94. Since `q>94`, this is a convex combination. It preserves the linear model and all three complete inequality families; it supplies no Boolean selection or induced path. The manuscript keeps this distinction explicit.

3. **The three complete-family deductions are correctly stated.** Occupancy potentials are used on the path obtained by deleting one cycle edge; adding that edge gives twice the cycle's nonselection sum, hence a sum at least one. Feasible source-to-sink flows require no maximum-flow optimality: conservation and arc capacities bound the flow by every separating cut, whose capacity is `B+E`. For disagreement parity, switching copies on an odd edge subset ends in the opposite copy of the starting vertex. Arc potential inequalities telescope to cost at least one, yielding the stated odd-subset inequality. A separate potential for each possible starting vertex is sufficient. The relevant counts, 337 occupancy potential systems and 158 flow/parity potential systems per root, agree with the audit summaries.

4. **The first-step restrictions match the saved fourteen certificates.** The seven root-0 neighbours are `2,4,8,16,32,64,128`; the seven root-78 neighbours are `14,74,76,79,94,110,206`. Every decimal in the main table matches `first-summary.json`. Exactly three upper bounds are below 94: `0->16` at 92.569610, `78->14` at 93.517327 and `78->74` at 93.927558. All eleven other upper bounds exceed 94. Selection of one root neighbour forces the other six to zero under the root degree/product constraints, as the separate coverage audit records. Exclusion of three branches does not establish feasibility of any remaining branch; both texts say they remain unresolved.

5. **Verification scopes remain distinct.** The general Boolean closed-cycle argument has an accepted Lean receipt. The finite models, rows, rational points, potentials and flows have independent exact native-arithmetic audits. The manuscript does not claim an end-to-end Lean assembly of those numerical arrays. The maintained global interval `191 <= a(9) <= 233` remains unchanged and the independent contributor-chain rebuild remains pending.

## Minor wording recommendations

- Short source line 304: replace “The 93-edge partner needed for 192 remains possible” with “The 93-edge partner needed for 192 remains unresolved.” The surrounding text is mathematically clear, but the replacement avoids any suggestion that a partner's existence has been established.
- Main source lines 7760–7763: “unresolved numerical assembly” can be made more precise as “the remaining Lean assembly of the numerical arrays.” Exact native assembly/arithmetic has already passed its separate audits; the remaining distinction concerns the end-to-end Lean interpretation.

These are wording refinements, not objections to the deductions. The review does not certify rendered layout, external references, the complete archived upper-bound chain, or native search traversal.

## Addendum: final wording revision

Both recommendations are applied. The short explanation now states that the 93-edge partner “remains unresolved”; the main verification passage now specifies “the remaining Lean assembly of the numerical arrays.” Reversing these two replacements in memory reproduces exactly the two originally reviewed source hashes, confirming that no other source bytes changed. The initial review and its hashes above remain historical evidence.

Final editor SHA256 values are:

- `snake9_research.tex`: `09a30206191809ba80a7d6ee11af6fcd3fb99e589d84243f970da182a8a170bf`.
- `snake9_frontier_explanation.tex`: `adbac0716c6ee01d61f2b801e4809d10f19e69c0ee80c04da728378df860873d`.

Each final editor file has exactly the same hash as its corresponding `E:/Snake-in-a-box/paper/` mirror. Both wording findings are resolved; the mathematical review conclusions and verification limits are unchanged. No manuscript edits, compilation or software tests were performed in this addendum.
