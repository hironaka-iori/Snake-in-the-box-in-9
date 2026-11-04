# Appendix review for revision 156

Reviewed the complete appendix and bibliography, source lines 3140–6491, against `milestones/155-share17-replay/COMPLETION.md`. Source SHA-256: `b3b06d3df379436f81b59d723d80bd01902d566e6d0617ceb860b155e4186e80`.

Coverage: earlier fixed-graph comparisons; successive count-sum and occurrence-credit refinements; historical certificates; earlier complete and five-window models; the radius-four 236 proof; six-direction pair caps; all intermediate geometric proofs and classifications; threshold counters; the 238 proof and every row of its 175-window catalogue; conditional research targets and the 196 conjecture; construction criteria and every construction experiment; all local-model diagnostics; all explicit transition sequences, vertex lists and blockers; both return witnesses; witness-verification procedure; every row of the 55-rule history-share catalogue; sharp pair and odd-length witnesses; all bibliography entries through the end of the document. One truncated read was completed by rereading lines 5629–5669.

This was an editorial and logical review of the existing record. No Lean, TeX, solver, graph-array, Git or external-source operation was performed. The paper was not edited. No historical theorem or certificate was independently reproved. A text-only whole-source scan found no duplicate labels, missing reference labels, duplicate bibliography keys or missing citation keys.

## Recommended prose changes

1. **Identify historical weight profiles once, before the first appendix comparison.** The unqualified labels “completed local floors” and “completed shares” can now be read as including the universal 012032 floor 16 and the count-conditioned floor 17, although their saved means predate these results. Add after line 3146:

   ```tex
   Throughout the historical comparisons, ``completed floors'' names the
   share profile used in the stated calculation. Its recorded weights and
   means are retained; later share theorems do not update those calculations
   automatically. The universal $012032$ floor 16 and the count-conditioned
   floor 17 are established separately in the current account.
   ```

   Keep every saved mean, potential range, table row and mathematical statement unchanged. This clarification also covers the successive profiles in Appendix~\ref{sec:sum-refinements}.

2. **Repair the displaced comparison-table pointer, lines 3211–3212.** Replace both sentences with:

   ```tex
   The three certificates for those specified profiles have the following
   open-walk data. Their means and ranges use the unscaled weight units of
   the comparison table in Section~\ref{sec:current-model}.
   ```

   The relevant table is at lines 2406–2416; it is no longer a preceding table in this appendix.

3. **Replace the stale count of pending share targets, lines 3858–3859.** Use:

   ```tex
   Floor $18$ remains the requirement for $012034$ in the retained
   conditional profile. The four remaining local share targets are
   $012034=18$, $012301=16$, $012340=16$, and $012345=16$.
   ```

   Milestone 152 completed the universal 012032 floor 16. Milestone 155 completed the conditional floor 17 with its count hypotheses and reversal; neither result proves the four listed targets or a full-graph potential. This replacement does not alter the historical nine-cycle obstruction or its formulas.

4. **Separate the share-13 certificate from the necessary-threshold argument, lines 3903–3905.** Replace the final two sentences with:

   ```tex
   No actual-snake share-$13$ theorem is claimed from this partial replay.
   The preceding cycle-and-subwalk argument supplies the necessary threshold
   for the fixed graph comparison. Neither calculation gives a new global
   upper bound or establishes an optimal range on the full graph.
   ```

   The partial Boolean replay itself does not establish the necessary threshold. That conclusion comes from Proposition~\ref{prop:share-fourteen-obstruction} and its preceding discussion.

5. **Replace prospective language in the historical 241 discussion, line 4852, final sentence.** Use:

   ```tex
   The later refinements track transitions, use radius four, and retain the
   empty-square term $s_0$.
   ```

   These steps already appear in the paper; calling them “the natural next refinements” makes this historical paragraph read as the current research agenda.

6. **Repair the displaced seven-centre model pointers.** In line 5738 replace the first sentence with:

   ```tex
   The first subsection records the earlier seven-centre finite-model result
   discussed in Appendix~\ref{app:historical-comparisons}; the second preserves
   its preceding cycle.
   ```

   In line 5741 replace the second sentence with:

   ```tex
   Directions and count symbols specify the states described in
   Appendix~\ref{app:historical-comparisons}.
   ```

   Section~\ref{sec:common-budget} now supplies the charge accounting, whereas the state construction is at lines 3148–3163.

7. **Make the time reference explicit in the diagnostic history paragraph, line 5850.** Replace the first sentence with:

   ```tex
   The state graph used at that stage records seven transition directions
   and the last four singleton-count symbols.
   ```

   “The existing state graph” can otherwise be mistaken for the current retained graph.

8. **Qualify an obsolete bibliography status at its recorded cutoff, line 6389.** Keep the complete entry, title, date and URL, replacing only its final sentence with:

   ```tex
   The final stronger occurrence assembly was incomplete at this cutoff;
   research record 137 supplies the later completed twenty-four-window bound.
   ```

   The immediately following `count24archive` entry identifies that completed record. The older bibliographic item should remain cited and retained.

## Additional observations

- Lines 3236–3240 preserve the distinction between a represented potential with checked range and its pending full edge certificate. Retain it. It does not establish minimal range for the newer floor-18 profile.
- Lines 3888–3950 correctly delimit milestone-143–146 certificate histories. Preserve their cutoff statements and historical module counts. They concern the still-unfinished 012034 and 012301 local proofs; milestone 155 does not complete those proofs.
- Lines 3619–3623 concern a different proposed 012301 count exclusion. Its pending status is not contradicted by the completed 012032 share theorem.
- The 196 conjecture is explicitly an extrapolation, requires both construction and exclusion for optimality, and remains separated from the maintained interval. Construction searches consistently distinguish feasible witnesses, restricted exclusions and unresolved runs.
- Keep the entire 175-window and 55-rule tables, witness strings, vertex lists, blocker lists, mathematical statements, formulas, labels and citation keys. Their definitions are used locally or identify finite proof data; this review found no safe deletion of a mathematical definition that would improve clarity without weakening the account.
- The 49-pair state description at lines 4828–4829 is followed by a check over `8^3` tuples, and the next paragraph uses `8^4`. The prose does not explain the larger checked domain. This is a minor presentation question for the saved source evidence, not a justified mathematical correction from this review. Leave the formulas and asserted test counts unchanged unless that evidence is inspected.
- Bibliographic labels and references resolve in the source. Some archives use branch URLs or local record paths; those links were preserved and were not tested remotely. No access dates or publication claims should be refreshed from this review alone.
- No major reordering is necessary. The appendices already separate historical comparisons, geometric proofs, experiments and explicit data. The recommended cross-reference and cutoff changes address the main reading ambiguities without moving proof material.

The reviewed appendix supplies no new global bound. The maintained 191–235 interval keeps the contributor-proof versus pending-independent-rebuild distinction stated in the current main text. The 1358 reference refutations and complete potential remain separate unresolved obligations for the conditional 234 route.
