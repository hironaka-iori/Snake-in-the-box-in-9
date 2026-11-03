# Exact share-floor sensitivity and the next charging target

The proposed reduction of the 012032 floor from 16 to 15 cannot be repaired by any uniform credit on the existing graph event in the original 97 graph. The obstruction uses two saved cycles and the new 149 zero-event walk. Its rows have now been independently reconstructed from the original arrays. This closes the proposed intermediate-credit test without another graph search.

No Lean, solver, graph search or Git operation was invoked in this investigation. Python used exact integer and rational arithmetic on saved cycles and walks. The root's full 147 replay was left untouched. The detailed new 149 audit is in `milestones/149-share-credit-tradeoff/audit/graph-review.json` and `.md`.

## The two-cycle sensitivity from milestone145

Fix the 012301 floor at 16. Write \(H\) and \(G\) for the 012032 and012340 floors, and \(C\ge0\) for the existing occurrence credit with allowance 24. Keep the other weights of the saved144 profiles fixed.

The eleven-cycle has three affected shares initially zero and one initially seven. Its total increases by

\[
\Delta(H)=3H+\max(0,H-7),
\qquad \Delta(H)=4H-7\quad(H\ge7).
\]

The fourteen-cycle and its first two edges give

\[
7\mu\le3456+G,\qquad R\ge2\mu-512.
\]

The eleven-cycle gives

\[
11\mu\le5399+\Delta(H)+4C.
\]

A comparison below235 requires \(227\mu>111960+24C+R\). Eliminating \(\mu\) and \(C\) gives the necessary conditions

\[
G\ge12,\qquad159G+42\Delta(H)>3874.
\]

For \(H\ge7\), the latter is \(159G+168H>4168\). In the more general notation of milestone145, the relation is

\[
325F+159G+42\Delta(H)>9074.
\]

Exact rational evaluation of every proper cyclic subwalk of these two saved cycles gives the following complete survivor table in the integer box \(0\le H\le16,4\le G\le16\). It concerns these two cycles only.

| \(G\) | \(H\) surviving with a nonnegative real credit | \(H\) surviving with zero credit |
| --- | --- | --- |
|4 through11|None|None|
|12|14 through16|15,16|
|13|13 through16|15,16|
|14|12 through16|15,16|
|15|11 through16|15,16|
|16|10 through16|15,16|

For each listed credit-allowed pair, the witness parameters are

\[
\mu=\frac{3456+G}{7},\quad
C=\max\left(0,\frac{11\mu-5399-\Delta(H)}4\right),\quad
R=2\mu-512.
\]

All 292 proper cyclic-subwalk inequalities were checked for each of the 221 grid pairs. The table is not a full-graph feasibility statement. In particular, \(H=10,G=16\) passing this table is insufficient evidence to weaken a local theorem target.

Sources: `144-countfree-share18/data/share18-impact/results.json`, `144-countfree-share18/data/share18-credit601-over36/results.json`, and the independently audited identities in `145-countfree-012301/data/joint-floor-review.json`.

## What the earlier full graph adds

The paper's least-floor discussion, Section `sec:least-floors`, uses the original 4,947,008-edge graph and its unchanged global boundary budget. Its exact integer floor box is recorded in `97-geometric-credit-integration/floor-sensitivity/012034-minimum/integer-floor-box.json`. Without occurrence credit, the only sufficient integer vectors in that box are

\[
(16,h,16,16,16),\qquad h\in\{18,19,20\},
\]

in the order 012032,012034,012301,012340,012345. This is a finite-graph result; the local floors and remaining graph-to-snake certificates retain their stated proof obligations.

Re-evaluating the saved walks with 012034 fixed at 18 gives:

| Saved walk | Length | Events | Deficit at \(\mu=496\) |
| --- | ---: | ---: | --- |
|012032 one-unit witness|69|31|600,632,664 at \(H=16,15,14\)|
|012340 one-unit witness|77|0|600 at \(G=16\);632 at \(G=15\)|
|012034 floor17 witness, reweighted at 18|51|0|602|

For a walk with length \(k\), uncredited weight \(W\) and \(n\) events, the unchanged mean496 cycle implies that a successful comparison needs

\[
(24-n)C<632-(496k-W).
\]

The 51-edge walk gives \(C<5/4\). The 69-edge walk gives \(C>0\) at \(H=15\), and \(C>32/7\) at \(H=14\). The 77-edge walk excludes \(G\le15\) for every nonnegative credit. Before the new 149 witness, only \(H=15,G=16,0<C<5/4\) remained as a possible weakening in this integer box. All 11 fully specified older walks examined allow range 602 at \(H=15,G=16,C=1\); their agreement did not establish a global potential.

The old and later graph statements must remain separate. The144 removal set deletes65 row occurrences from the 69-edge walk and3 from the 77-edge walk. The smaller graph also retains additional geometric hypotheses, including the unresolved six-count25 premise.

## The new combined obstruction

The attempted pointwise repair fails: a saved full-graph row, edge 4719073, has shape012032, counts \((6,6,6,6,2,3)\), base weight 365, and weights 376 and 375 at floors16 and15. Its event is false. The root's separate all-edge check reports 43,003 such non-event changes among 66,567 changed edges; this investigation did not duplicate that full scan.

The root then found the 28-edge zero-event walk saved in `149-share-credit-tradeoff/data/new-potential.json`. This investigation independently checked its original rows, every count symbol, all directions, all weights and adjacency, along with the three-cycle and eleven-cycle. The exact inequalities are

\[
\mu\le496,\qquad11\mu\le5452+4C,\qquad28\mu\le13280+R.
\]

They imply

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}\ge235.
\]

Indeed, the numerator minus 235 times the denominator is at least
\(65968-133\mu\ge0\). The scalar relaxation attains equality at
\(\mu=496,C=1,R=608\). Thus no intermediate credit, including one half, can repair this weakened floor within this model. The half-credit computation was cancelled before launch.

With the other floors fixed at their current targets, monotonicity extends the obstruction to \(H\le15,G\le16\). The separate 77-edge zero-event witness excludes \(G\le15\) even at \(H=16\). Consequently, only \(H=G=16\) remains in that box for the existing uniform-credit scheme. This result concerns the original graph: the144 removal set deletes three rows of the new walk and two edges of the three-cycle, so the same obstruction is unavailable there.

## One recommended bounded task

Keep the 012032 target tied to the actual low-pair event, rather than weakening a coarse graph floor and retuning its existing event credit. The useful single local statement to investigate is

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})
 +\mathbf1_{\{\alpha_{r+2}+\alpha_{r+4}\le9\}}\ge16
\]

on a canonical012032 window. It asks for share at least 15 universally and at least 16 when the actual pair sum is at least 10. Both requirements remain unproved here. A first bounded test is the high-pair branch: add actual pair sum at least 10 to the existing share-cap15 local system, with symbol 6 interpreted as an interval throughout. This is a precise local certificate target; no proof-size or runtime improvement is asserted.

The reason for this target is mathematical. The checked 24-window theorem bounds the number of actual low-pair exceptions. If the displayed local statement and the other conditional-profile premises hold, the existing floor 16 potential can be charged directly against actual shares with total error at most 24. Its current margin 30 then leaves margin 6:

\[
4696m\le1098960+8\cdot496+602+24
=1103554<235\cdot4696=1103560.
\]

This is a proposed conditional deduction, not a completed local theorem or global bound. It uses the actual pair event, including windows whose stored symbol 6 represents an actual count6 or7. The tested graph event deliberately excludes all symbol 6 cases; the new zero-event walk therefore does not refute this proposed local statement. Six of its 012032 rows have that exact ambiguity. No graph modification or second research route is needed to state and test the local target.

## Verification record

The independent audit receipt is `149-share-credit-tradeoff/audit/graph-review.json`, SHA256 `29c1a4af5863eea9b8144953b4dc3b152368c2a86c744dccc8091c0c2507f418`. It pins the original source graph, six array hashes, direction catalogue, all selected rows and the removal-set comparison. The new walk source is SHA256 `9dca9beef99ef182329deaf9b73d83c4fe94ce2a9e51a7c4fe61cd471ecf4245`. The root separately reports successful Lean checks of the five arithmetic statements in `CreditTradeoff149`; no Lean run was performed by this investigation.

No claim of novelty, realizable snake construction or improved unconditional upper bound is made.
