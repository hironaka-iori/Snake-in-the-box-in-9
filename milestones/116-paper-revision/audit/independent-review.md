# Independent review of the manuscript changes

## Reviewed version and scope

Final reviewed manuscript SHA256: `5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f`. The editor source and repository mirror were both checked at this hash after the clause-count correction below. The initial full comparison inspected version `13295441c1e9fe967507d9dc0c5a37137ef516c826ff6ff89a2a30c1eeb748d3`, using every changed hunk against `data/paper-before.zip`, member `snake9_research.tex`, whose prior source hash is `f649b4dfc0b3f11958105517d00f567db591517e5a3434e1dfad3cfc212b3429`.

Backup archive SHA256: `20b80ea94f724f06a18de267054d0aa364d7cdd76aee5483a7cc8d0afa764b47`.

Revision-script SHA256 after correction: `a1fd794ccc186077727908d430a6e7f1c0ed9be55243c94e1662e7c888dc5e6c`. Its initial reviewed hash was `6802d7a6a15f735e3437a3a5351fe0c02e088eb166a0f69415d46c47bbee9c58`.

This was a bounded source and evidence review. No compiler, solver, test suite, full graph scan or certificate replay was run. The source comparison contains no appendix changes or changes to the existing theorem statements. This review does not establish compilation or page layout.

## Corrected precision finding

In `sec:sum-refinements`, the initial reviewed version said the selected $012310$ proof uses 5,067 input clauses. The selected input actually contains **5,114 clauses, of which 5,067 are used**. Both `115/data/replay-core1.json` and `115/data/total-plan.json` give 5,114; the former separately records `used_input_clauses = 5067`. The final source now says “proof uses 5067 of its 5114 input clauses,” and this correction was read directly. The finding is resolved. It does not affect the contradiction or its pending Lean status.

An optional clarification would describe the “total-count counter” as retaining 105 occurrences, instead of “its five counters.” The 105 occurrences are the concatenation of the five 21-entry corner lists; their repeated entries are retained in the counter for the total. The current wording also counts those occurrences across the five lists, so this is a clarity suggestion rather than a mathematical error or an outstanding correction requirement.

No substantive mathematical defect was found in the changed statements or proofs.

## Local statements and reversal

`prop:recent-counts` has the correct positions and thresholds for all three patterns. In particular, the $01234$ row leaves its third count unrestricted, and the $012340$ three-count exclusion does not replace the separate exact tuple $(5,5,2,4,5)$. The stated 120/75, 441/270, 2040/11711 and 1664/2007 clause/deduction counts agree with the recovered certificates. The finite-subset lemma supplies the stated cycle exclusions.

Joint reversal of directions and count order is essential and is stated correctly. The actual-snake and both-orientation claims for these exclusions agree with the saved checked interfaces, including the explicit forward and reverse statements in `MiddleCount111`. The proof correctly avoids a collective reference-catalogue hypothesis.

`thm:outer-four-sum` matches the closed `ActualSum112.actual_outer_sum`: a fitting $012314$ window and middle count at most two imply outer sum at least 19. Its canonical vertices, 84 literal occurrences, 70 distinct corners and 3306/7020/367588 certificate counts are correct. Multiplicity is preserved. The claim about the reversed segment is mathematically justified by reversing the whole snake: the middle stays middle and the outer positions are permuted. The manuscript does not claim that a separately implemented graph-orientation guard for this sum theorem has passed Lean. That distinction must remain.

## Budget and global scope

`prop:four-five-budget` correctly uses $\alpha_i=b_i+\delta_i$, nonnegative coefficients and $4a+c\le120$. An outer-four deficit, outer-pair deficit and total-five deficit are each bounded by the same weighted excess. Their maximum is safe; adding all three would require additional capacity. Distinct fitting starts make each fixed shift injective, proving the summed capacity bound.

The subsequent boundary paragraph correctly combines the omitted clipped-count total 21, excess budget and fivefold share overlap. Its arithmetic gives $W+2520\le5G_{12}$ and then $W+4200m\le1098960$. Applicability still requires valid local count and share bounds at the stated positions. The paragraph and the later refinements section explicitly preserve that requirement, so the generic budget is not presented as a completed interpretation of the revised graphs.

The preceding baseline graph definitions, weight interpretation and existing bound assembly remain unchanged. New references to the baseline prevent old cycle obstructions from being silently applied to different graphs.

## Reference and candidate status

The revision consistently retains the full catalogue size 1,378 while recording 12 discharged entries and an equivalent remaining obligation of 1,366 entries. The table indices and original retention proposition are unchanged. The updates in the abstract, main argument, closure and verification sections are consistent.

The ten-row sum table matches the final native experiment. Only its $012314$ row is asserted as a completed actual-snake theorem. The pair row still requires its local contradiction; the $012310$ proof distinguishes native replay and checked concrete semantics from the unfinished Lean contradiction and final composition. The proposed $012345$ lower bound 23 is clearly a native candidate supported by five validated cuts, with independent negative replay and Lean checking outstanding.

The two local witnesses are described with the correct limitation. In particular, $(6,3,6,2,6)$ totals 23 and its component sizes $43,27,24,9,1,1$ total 105 vertices. These local forests do not provide complete snakes or establish sharpness for complete snakes.

## Numerical comparisons and cycle argument

The four displayed completed-floor mean/range pairs agree with the saved experiments:

$$
(484,557),\quad(484,557),\quad(2424/5,2881/5),\quad(6309/13,7656/13).
$$

The conditional profile remains $(496,602)$. The exact fractions $4781536/20303$ and $551765/2348$, and their integer parts 235 and 234, are correct. The text identifies the all-edge checks as conditional finite-graph calculations and does not upgrade the completed-floor label to a completed snake bound.

The final universal-22 cycles have 26 and 6 edges and no $012345$ window among the 64 placements. Raising only that rule's lower bound preserves those cycles and their weights; remaining edge weights cannot decrease. Thus the existing potential and attaining-cycle argument preserves the exact means. The manuscript correctly refrains from claiming a new all-edge run, a new deletion count or minimality of the inherited ranges. The limitation concerns direct refinements confined to the absent shape in this fixed model; it does not preclude consequences involving other shapes or a changed global accounting argument.

The threshold equivalences match `Comparison114`. The displayed differences are correct:

$$
111960\cdot13-227\cdot6309=23337,\qquad116160-226\cdot496=4064.
$$

Therefore range reduction alone cannot improve the two displayed integer comparisons, even at zero range. No new global upper bound is claimed.

## Conclusion

The final revision is mathematically consistent with the reviewed evidence, and the input-clause precision finding has been resolved. Its theorem, conditional and unresolved labels are appropriate. No substantive finding remains open. This report covers the final source hash stated above; it does not establish compilation or visual rendering.
