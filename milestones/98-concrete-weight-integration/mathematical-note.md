# Actual graph weights and the remaining upper-bound assumptions

The maintained interval is
\[
191\le a(9)\le235.
\]
The upper bound uses the inspected contributor theorem and archived audit;
its complete independent rebuild remains pending. This round connects the
local share bounds, actual graph weights, boundary saving and total charge.
All 12 modules passed Lean, with 80 theorem audits including reused roots
and auxiliary statements. No new unconditional numerical bound is claimed.

## The weight of an actual step

For a fitting nine-transition window beginning at position $r$, the entering
count belongs to vertex $r+8$. All applicable share bounds concern precisely
the five vertices at positions $r+4,\ldots,r+8$. Their maximum is therefore at
most the sum of those five shares. The alternatives are the geometric bound,
the history rules, the four count-dependent rules and their reversals, the
share-120 rule, and the chosen count-independent floor.

Reversal acts on both the directions and the five count symbols. A symbol
equal to six retains the interval $[6,21]$. The numeric suffix code is the
last five base-six digits, represented by the remainder modulo $7776$.

Writing $w_r$ for the actual edge weight gives
\[
w_r\le120\alpha_{r+8}
       +\sum_{j=4}^{8}\sigma_{12}(x_{r+j}),
\qquad r+9\le m.
\]
The coefficient 120 multiplies the singleton count. The share values already
have scale 12, so there is no additional factor 12 on the local credits.

The two floor profiles are:

| Six-transition shape | Completed floor | Conditional floor |
| --- | ---: | ---: |
| 012031 | 16 | 16 |
| 012032 | 0 | 16 |
| 012034 | 0 | 18 |
| 012301 | 0 | 16 |
| 012304 | 16 | 16 |
| 012310 | 12 | 12 |
| 012314 | 16 | 16 |
| 012340 | 0 | 16 |
| 012345 | 12 | 16 |

A zero floor adds no count-independent credit; all other bounds remain in
the maximum. The completed profile has no unfinished local-share premise.
The conditional profile retains five refutations, with respective share caps
$15,17,15,15,15$. In particular, cap 17 supplies the required floor 18 for
$012034$. No assertion that these five refutations have been proved is made.

## Boundary and total charge

For $m\ge9$, the entering counts omit the first eight vertices and the final
endpoint. The two endpoint bounds contribute at least eight; three disjoint
internal pairs contribute at least twelve; the remaining internal vertex
contributes at least one. Thus at least 21 singleton counts are omitted:
\[
\sum_{r=0}^{m-9}\alpha_{r+8}+21\le T.
\]
Every path vertex occurs in at most five charged windows. Summing the local
weight bound, and writing $W=\sum_{r=0}^{m-9}w_r$, gives
\[
W+2520\le120T+5\Sigma=5(24T+\Sigma).
\]
The existing empty-square charge bound is
\[
24T+\Sigma+840(m+1)\le221136.
\]
Consequently,
\[
W+4200m\le1098960.
\]
The completed profile supplies this budget for every actual snake with
$m\ge9$. For the conditional profile, the only additional local assumptions
are the five refutations listed above. The budget itself needs no graph
coverage or reference-catalogue assumption.

## The graph walk and potential

The row key records direction, history and all six count symbols. The
strengthened walk statement preserves this full key and both endpoints at
one common row index for each step. Endpoint equality alone cannot identify
the weight, since distinct full keys can have the same endpoints.

The actual walk in the defined graph retains two reference-catalogue
refutation assumptions. All 127 coverage classes and their assembly were
completed in the preceding round. A potential must satisfy its edge
inequality on every row of this defined graph, including any accepted rows
outside the saved graph array.

If a nonnegative potential of range at most $R$ satisfies
\[
P+\pi(v)\le w(u,v)+\pi(u)
\]
on every defined row, summing along the actual walk yields
\[
P(m-8)\le W+R.
\]
Together with the charge budget this gives the following conditional
conclusions:

| Profile | Slope $P$ | Range bound $R$ | Result after the stated graph assumptions |
| --- | ---: | ---: | ---: |
| Completed | 483 | 551 | $m\le235$ |
| Conditional floor 18 | 496 | 602 | $m\le234$ |

The second comparison is
\[
4696m\le1103530<4696\cdot235.
\]
Short snakes with $m<9$ satisfy either numerical conclusion directly.

The numerical conclusions retain concrete potential and range hypotheses.
Their verification on every defined row is still required. The existence of
the abstract assembly does not discharge those finite certificate obligations.

## Evidence and next work

An independent integer reconstruction agrees with all 4,947,008 saved full
keys in 791 contexts, for both profiles and both endpoint columns. The
completed and conditional weight hashes agree with their earlier certificates.
This computation concerns the saved arrays; it does not check the Lean
potential hypotheses on the full defined graph.

The immediate next step is to certify those potential inequalities and range
bounds in the same graph and weight definitions. The two reference-catalogue
closures and the five conditional share proofs remain explicit obligations.
Any new proof attempt for the $012034$ floor 18 must preserve the old
target-20 evidence and use separate files.

Exact checking status, source and dependency hashes are saved in
`data/proof-summary.json` and the individual compiler receipts. The source
ports of the five old credit roots preserve every byte. Existing proof
objects are reused; this round is not a complete clean rebuild of their
dependencies. The paper remains revision 96, with its authors and hyperlink
settings unchanged. The next scheduled full revision is milestone 106.
