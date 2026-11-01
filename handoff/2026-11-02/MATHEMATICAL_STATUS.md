# Mathematical conclusions and remaining obligations

## Problem and conjecture

A snake is an induced path in the binary hypercube \(Q_9\): successive
vertices differ in one coordinate, all vertices are distinct, and
nonconsecutive vertices are nonadjacent. Let \(m\) denote its edge length
and \(v=m+1\) its number of vertices. The target is the maximum \(a(9)\).

The project has not determined that maximum. The retained interval is
\(191\le a(9)\le235\), with the provenance qualifications in `START_HERE.md`.
The conjecture \(a(9)=196\) remains weakly supported. The first eight values
\(1,2,4,7,13,26,50,98\) admit competing extrapolations. A doubling correction
in blocks of three predicts196, while an additive correction fits the same
data and predicts195. Neither extrapolation supplies a geometric argument.
Earlier searches produced no valid snake longer than191; near196-edge walks
with chords do not improve the lower bound.

## Empty-square accounting

Let \(s_0\) be the number of coordinate squares containing no selected vertex,
and let \(T\) count squares containing exactly one selected vertex, counted at
that vertex. The established incidence and path identities give
\[
T+2s_0+35v=9214,\qquad 39m+2s_0\le9200.
\]
The current route retains information from \(s_0\) rather than discarding it.

For a cube vertex \(q\), write \(e_0(q)\) for the number of empty squares
through it and \(d_S(q)\) for the number of its selected neighbours. For a
selected vertex \(x\), define
\[
\sigma_M(x)=\sum_{q\sim x}
\left\lfloor\frac{M e_0(q)}{d_S(q)}\right\rfloor.
\]
The denominator is positive in this sum. With
\(\Sigma=\sum_{x\in S}\sigma_{12}(x)\), double counting gives
\(\Sigma\le48s_0\). Thus the useful combined charge is
\(G=24T+\Sigma\). Milestone73 checks that the local certificate quantity
equals this global share quantity at each selected vertex.

Let \(\alpha_j\) be the singleton-square count at the selected vertex in
position \(j\), and use the truncated count \(b_j=\min(6,\alpha_j)\).
An internal count lies in \([1,21]\); endpoints have count at least4.
The symbol6 means the interval \([6,21]\). It must never be treated as
the exact value6 when applying a guard.

The graph uses five-centre share windows. Every centre is counted at most five
times. Combining applicable lower bounds for the same centre set uses their
maximum. Adding them would generally count the same share twice.

For the graph edge starting at \(r<m-8\), the entering count is \(b_{r+8}\)
and the share centres are \(r+4,\ldots,r+8\). The omitted count positions are
\(0,\ldots,7,m\), whose total is at least21 in the relevant range.
The existing accounting then gives
\[
W+4200m\le1098960.
\]
Here \(W\) is the sum of valid edge charges along the actual snake's graph
walk. Proving that this walk exists and that every stored credit is valid is
an essential remaining obligation for the current graph.

## Conditional potential calculation

A scaled potential inequality of slope \(p/d\), with integer-scaled range
\(R\), yields
\[
(p+4200d)m\le1098960d+8p+R.
\]
It excludes235 precisely when
\[
227p>111960d+R.
\]
The full mixed share catalogue has an exactly checked finite-model mean496
and potential range600. Its comparison bound is
\[
m\le\frac{137941}{587}<235.
\]
The integer consequence would be234. The strict exclusion margin is32.
This remains conditional on the missing local certificates, the complete
snake-to-graph interpretation and the graph-potential replay in Lean.

## Local share catalogue

A pattern records repeated coordinate directions up to relabelling and reversal.
It describes six consecutive transitions and their five internal centres.
Milestone73 proves that every actual six-transition snake window belongs to
one of the following nine types.

| Pattern | Target share | Current status |
|---|---:|---|
| 012031 | 16 | Lean-checked, including arbitrary labels and reversal |
| 012032 | 16 | Native refutation; Lean completion pending |
| 012034 | 20 | Native refutation; Lean completion pending |
| 012301 | 16 | Native refutation; Lean completion pending |
| 012304 | 16 | Lean-checked, including arbitrary labels and reversal |
| 012310 | 12 | Semantic batches and composition checked; selected refutation replay pending |
| 012314 | 16 | Lean-checked, including arbitrary labels and reversal |
| 012340 | 16 | Native refutation; Lean completion pending |
| 012345 | 16 | Share12 is Lean-checked; the stronger16 remains pending |

The checked count-conditioned share120 theorem is a separate rule for six
distinct directions with internal counts \((4,5,4,2,t)\), \(6\le t\le21\).
It cannot replace an unconditional floor for every window of that shape.

Adding only the currently completed rules to the previous audited local model
gives exact finite mean480 and range536. Adding the still-unproved012310
share12 rule gives mean483 and range551. Both comparisons yield an integer
upper value235, and both retain the separate graph-interpretation obligation.
The hypothetical improvement of the mean is a reason to finish that case;
it is not itself a new unconditional bound.

## New short-walk obstruction

Six weakened catalogues retain a three-edge cycle of total weight1488, forcing
every admissible normalized constant slope \(p\le496\). Each also has a
saved walk with \(L\le17\) and \(D=496L-W\ge632\). Telescoping gives
\[
227p-R\le(227-L)p+W\le112592-D\le111960.
\]
Consequently, no change of constant slope or global potential range can make
the current234 arithmetic succeed on those entire relaxed graphs. The generic
rational implication is Lean-checked; the concrete walks and cycle membership
have exact Python array checks. See milestone74 for the six witnesses.

This result is restricted. It does not prove that all target floors are
numerically minimal after reoptimization, that the witness walks arise from
actual snakes, or that other accounting schemes fail. Reachability restrictions,
state-dependent endpoint costs and additional geometric constraints remain
possible ways to change the conclusion.

## Exact graph and missing global proof

The current model has1,601,856 states and4,947,008 edges. A state stores
**five** truncated counts; an edge stores **six**. There are132 eight-direction
shapes,505 nine-direction extensions and74 additional nonempty history classes:
\[
(132+74)6^5=1601856.
\]
The source count tuple is \((b_{r+3},\ldots,b_{r+7})\), and the target tuple
is \((b_{r+4},\ldots,b_{r+8})\). History starts empty and records the longest
listed suffix of the already-read direction IDs. Contributor seven-centre
count-only tables have different state dimensions and cannot be substituted.

Two substantial global steps remain:

1. Construct the graph walk for every actual snake. Prove numeric state coding,
   the history invariant, exclusion lookup coverage, compatible eleven-direction
   variant coverage, and validity of the maximum of all applicable credits.
2. Replay the exact full potential and range in Lean, bound to the same source
   arrays. Then use the existing overlap, omitted-count and telescoping lemmas.

The four new state-shift identities settle source/target/suffix direction
normalization, but do not settle those two steps. Existing local theorems and
generic budgets are reusable. A successful import of a conditional theorem,
or a theorem file called `UpperBound234`, does not discharge its hypotheses.

## Research priorities

Finish the pending012310 proof first if continuing the certificate track.
In parallel work by another agent, the precise graph interpretation is now a
well-specified task with identifiable missing lemmas. Avoid rerunning broad
searches or recomputing potentials on the six obstructed relaxations without
changing an assumption. A fresh independent rebuild of the contributor235
closure would strengthen confidence in the retained interval, even though it
would not lower the numerical bound.

The exact optimum, a construction beyond191, an unconditional234 theorem and
the conjectured196 all remain unresolved at this checkpoint.
