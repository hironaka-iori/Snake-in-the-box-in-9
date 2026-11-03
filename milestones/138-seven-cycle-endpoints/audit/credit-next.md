# Saved-cycle check for a uniform suffix credit

This review used saved JSON rows only. No graph array, potential array, solver, or Lean compiler was loaded or run. The arithmetic below is conditional on the stated graph, credit rule, occurrence allowance, and comparison formula.

## Indexing and event count

A row records nine directions and six count symbols at local vertices 3 through 8. For a suffix event, canonicalize `directions[3:9]` in both orientations and test the shape `012032`. Its relevant count pair is `counts[2], counts[4]`, corresponding to local vertices 5 and 7. Reversal swaps these two counts and leaves their sum unchanged.

For an event certified directly by the stored symbols, require both counts below 6 and their sum at most 9. A symbol 6 denotes an actual count in `[6,21]`; a clipped sum at most 9 alone cannot certify the actual upper bound. Assigning credit only to the exact pairs is sufficient for an occurrence allowance that bounds all actual pairs of sum at most 9.

The prefix test uses `directions[2:8]` and `counts[1], counts[3]`. It is recorded separately and receives no second credit for a window already represented as a neighbouring suffix.

| Saved cycle | Length | Suffix events | Prefix matches |
|---|---:|---:|---:|
| milestone121 completed 18-cycle | 18 | 0 | 0 |
| milestone131 completed four-cycle | 4 | 2 | 2 |
| milestone131 conditional seven-cycle | 7 | 0 | 0 |

The 18-cycle and seven-cycle contain no matching `012032` shape at either placement, so there is no clipped-count ambiguity in either zero count.

The completed four-cycle has these exact pairs:

| Row | Edge ID | Placement | Pair | Physical phase in the four-row period |
|---:|---:|---|---|---:|
| 0 | 2222328 | Suffix | `(4,5)` | 1 |
| 1 | 147674 | Prefix | `(4,5)` | 1 |
| 2 | 2220858 | Suffix | `(5,4)` | 3 |
| 3 | 146782 | Prefix | `(5,4)` | 3 |

Thus there are two events per four-edge period, not four. Both event pairs have sum exactly 9.

As an additional check, the earlier milestone121 conditional four-cycle has two suffix and two overlapping prefix pairs, `(3,5)` and `(5,3)`. Those are earlier pair-sum-eight rows. They are not the current milestone131 four-cycle and do not establish its current survival or weights.

## Effect of adding a credit

Suppose the only weight change is addition of \(C\ge0\) to each certified suffix event. This is an additive rule on top of the existing weights; the formulas do not assume a replacement of the shared maximum used by the earlier charges.

The archived completed 18-cycle has current milestone131 comparison mean \(3011/6\). That value is recorded in `saved18_cycle_hypothetical_mean` in the milestone131 result. Its older milestone121 stored mean \(2915/6\) used earlier weights. With the current weights and the proposed credit, its mean stays

\[
\frac{3011}{6}+\frac{0}{18}C=\frac{3011}{6}.
\]

The current completed four-cycle has mean

\[
488+\frac{2}{4}C=488+\frac C2.
\]

Both cycles survive the exact full-nine exclusion considered in `graph-base-next.md`. Therefore, after that deletion and with unchanged other restrictions, any new completed-profile minimum \(\mu\) satisfies

\[
\mu\le\min\!\left(488+\frac C2,\frac{3011}{6}\right).
\]

The two comparisons agree when

\[
C=\frac{83}{3},\qquad 488+\frac C2=\frac{3011}{6}.
\]

This makes \(C=83/3\) a justified first candidate for a bounded graph test. It does not prove attainment of the target mean. Larger credits cannot exceed the unchanged 18-cycle comparison and, for a fixed allowance of 24 events, increase the allowance term. Smaller credits impose a lower four-cycle comparison, although their effect on the potential range would require evaluation.

The saved seven-cycle has no events. Before the new ordinary exclusion, its mean under completed-profile weights is \(3453/7\), as independently recorded in milestone132. Its conditional-profile mean is 496. Both are unchanged by this credit. The exact full-nine exclusion removes its edge 992157, so completion and justified application of that exclusion are necessary before using the higher target without this saved obstruction. The milestone132 fixed-graph limitation remains correct for its original graph; the proposed deletion changes its hypothesis.

## Conditional comparison arithmetic

Assume that a checked comparison has the form

\[
B=\frac{1098960+8\mu+24C+R}{4200+\mu},
\qquad \mu\ge0,\quad R\ge0,
\]

where the allowance of at most 24 credited occurrences has been justified for the actual snakes under consideration. This allowance and the graph-to-snake comparison are assumptions of this note, not results of its saved-row check.

At \(\mu=3011/6\) and \(C=83/3\), direct rational arithmetic gives

\[
B-235=\frac{R-7753/6}{4200+3011/6}.
\]

Consequently, the strict condition is

\[
R<\frac{7753}{6}.
\]

Equality gives \(B=235\) and does not give the next integer upper bound 234. If the comparison bounds an integer quantity and all hypotheses hold, the strict inequality gives that quantity at most 234. No new minimum, potential range, occurrence theorem, or actual-snake bound was established by this review.

## Input hashes

| Repository-relative path | SHA-256 |
|---|---|
| `milestones/121-replacement-window-pressure/data/pair-graph/results.json` | `7492ff3a45178740d3253c679bcdd2f5e7907be907f055f455e739cde0b327bf` |
| `milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json` | `157c1cd0751b487e220b954f441670839c50078167f54c83557f43f98fb8fd2d` |
| `milestones/132-odd-pair-endpoint/data/credit-limitation.json` | `5c38b530315591a5f2db4d0043c66cd167e98feeeee74de14144d9a85c231743` |
