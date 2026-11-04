# Full paper review for revision 166

Reviewed on 4 November 2026. Scope: editorial and mathematical consistency of integrating milestones 157–165, preserving established proofs and historical evidence. This review does not independently recheck every existing proof or run Lean.

## Inspected source

Read all 6,605 lines of `paper/snake9_research.tex` in bounded chunks, including the historical appendices, witness lists, complete share catalogue and bibliography. Re-read the portions lost to tool-output truncation. Reviewed source SHA-256:

`e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb`

Repository revision: `958068470c2f6f252f858b1661142d0746582d1b`.

Read the mathematical notes for 158 and 164, `163-share18-replay-continuation/ROUNDING_LOSS.md`, and 165's completion record. The authoritative editor file and repository mirror have the same paper content at this cutoff. No paper, preamble, author, or hypothesis-setting edits were made by this reviewer.

## Minimal revision locations

Line numbers refer to the inspected source, before insertion.

1. Abstract, lines 38–60: retain maintained interval 191–235 and independent-rebuild caveat. Add the alternative conditional comparison with 012034 floor 17, total rounding loss at least four, mean 4462/9 and range 5411/9. State that its local and graph interpretation premises remain unresolved. The existing optimum at floor 18 concerns the earlier comparison which discards the loss.
2. Overview, lines 107–116, and evidence table, lines 120–140: distinguish the original conditional 234 route from the floor-17 route with retained loss. Replace or shorten an existing comparison row rather than enlarging the nonbreaking table unnecessarily. The unconditional interval has not improved.
3. Immediately after the corner-share identity proof around line 610: expose the exact budget already implied by the definitions, then give the degree-based remainder decomposition. Use the existing sum of remainders; no named auxiliary quantity is necessary.
4. Count-free catalogue discussion around lines 1645–1750: qualify statements that floor 18 is the required target. It is required by the earlier comparison without the loss correction; floor 17 with a separate loss bound is now an alternative. Preserve the original table and its proof status.
5. After `cor:potential234`, around line 1968: insert the loss-retaining comparison, derived directly from the exact budget, window packing, and potential premise. This is the logical location for the general improvement, before the finite graph experiments.
6. After `sec:range156`, before `sec:closure` at line 3054: insert one concise subsection containing the floor-17 obstruction without loss (158), followed by the successful fixed-mean retained-loss comparison (164–165). Preserve the exact fixed-floor-18 optimum and its proof.
7. Closure section, lines 3054 onward: list the new loss-at-least-four premise alongside inherited local floors, reference refutations, retained count restrictions, applicable parity conditions, and graph interpretation/certificate obligations. Loss at least four alone does not establish 234.
8. Verification section, lines 3108 onward: replace the current-only 1,055-deduction description of 012034 near line 3237 with the current accepted 33,111 deductions and 2,734,960 references. The complete 13,224-clause interpretation and original-formula-to-checkpoint consequence are available. Accepted continuation consists of 448 segments in 14 groups, with 216 accepted modules. Remaining: 112,104 deductions and 11,975,921 references. Neither the final contradiction nor actual-snake/reversal share theorem follows from this prefix.
9. Add precise research-record bibliography entries covering 158, 159–163, 164 and 165. A pinned URL under revision `958068470c2f6f252f858b1661142d0746582d1b` is available for these records. Do not put implementation identifiers or Lean module filenames into the mathematical body.

## Exact statements to integrate

The existing definition of the remainder gives

\[
G_{12}+840(m+1)+\sum_q r_{12}(q)=221136.
\]

For each corner q, every incident empty square uses two unselected neighbor directions, so

\[
e(q)\le\binom{9-d(q)}2.
\]

For d=7 this implies e≤1; for d=8 or 9 it implies e=0. Since 1,2,3,4,6 divide 12, the only positive-degree remainder contributions occur at degrees 5 and 7:

\[
\sum_q r_{12}(q)
=12\sum_{d(q)=0}e(q)
+\sum_{d(q)=5}(2e(q)\bmod5)
+5\sum_{d(q)=7}e(q).
\]

This follows by the finite degree cases and the existing d=0 convention. The degree-5 term must retain its modulus after aggregation. The saved nine-vertex path `(1,3,2,6,4,12,8,24,16)` has d(0)=5 and e(0)=6, giving remainder 2 instead of the invalid unrounded value 12. New Lean status should be stated only after the parent finishes the round-166 check.

The existing inequalities

\[
W+2520\le5G_{12},\qquad
\mu(m-8)\le W+R+24C
\]

now give

\[
(4200+\mu)m\le1098960+8\mu+24C+R-5\sum_q r_{12}(q).
\]

No change to the old corollary is needed: it remains a valid weaker consequence.

For the floor-17 graph, the nine-edge cycle has weight 4462 and no recorded occurrence events, while the saved nine-edge walk has weight 3861 and no events. Hence

\[
9\mu\le4462,\qquad R\ge9\mu-3861.
\]

The old comparison is therefore at least

\[
\frac{9931745}{42262}=235+\frac{175}{42262},
\]

for nonnegative mean and uniform occurrence credit. This is an obstruction, with no attainment claimed. It does not rule out the loss-retaining comparison.

For the retained conditional graph with 4,661,572 edges, exact native integer checks provide mean 4462/9 and range 5411/9. A 35-edge walk of weight 16751 forces

\[
35\cdot4462-9\cdot16751=5411,
\]

so this range is minimum at that fixed mean. Joint optimization over the mean is not claimed. With C=0 and total loss at least four,

\[
m\le\frac{9931567}{42262}=235-\frac3{42262}<235,
\]

which gives integral m≤234 under all inherited premises. At these parameters loss three gives 235+42/42262, so the comparison does require at least four to cross the threshold. The recorded Lean arithmetic checks do not prove the native all-edge potential inequalities or the positive-loss premise for snakes.

## Scope and preservation requirements

- Preserve the preamble, hyperref settings, three authors, old local proofs and complete printed witnesses.
- Preserve historical cutoffs, including the 144–146 prefix record. Do not globally replace every occurrence of 1,055, floor 18, range 602, or the earlier graph edge counts.
- The fixed-profile floor-box classification and 156 joint optimum remain valid in their stated model. The new comparison changes the accounting and weakens one floor.
- The retained graph inherits extra count and odd-length restrictions. When excluding 235-edge snakes, make explicit why that target lies in the relevant parity class; do not present this as a graph automatically covering all snakes.
- Universal positive rounding loss is unproved. The small-loss exclusions investigated in round 166 should be stated with the exact scope supported by the new proof receipt.
- The full manuscript is long but logically separates current results from historical derivations and restricted construction searches. No broad rewrite of those appendices is needed to integrate this ten-round update.
- Resource gates and compiler scheduling belong in the research record, rather than the main mathematical argument. A resource stop supplies no mathematical exclusion.

Only this review file was written. No Lean process, heavy graph computation, external browsing, or paper compilation was started.
