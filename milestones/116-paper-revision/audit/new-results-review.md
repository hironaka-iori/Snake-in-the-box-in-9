# Mathematical additions since the previous manuscript revision

## Scope and evidence

This review covers the saved README files, mathematical notes and proof summaries of milestones 107–115. It checks current source, object and log hashes against the successful receipts for `MiddleCount111`, `ActualSum112`, `SumBudget112`, `PairBudget113` and `Comparison114`. Their printed theorem dependencies contain only subsets of `propext`, `Classical.choice` and `Quot.sound`. No compiler, solver, graph scan or large certificate replay was run for this review. The dependency closures were not rebuilt. Exact input pins and the individual axiom lists are saved in `../data/new-result-pins.json`.

The additions should occupy a separate refinements subsection. The original graph, its weights and its global charge theorem should remain mathematically unchanged. Later native graph experiments do not yet have the complete checked interpretation needed to replace that graph in the main argument.

## Closed local restrictions and reference recovery

Write the snake as $x_0,\ldots,x_m$. A direction word denotes a coordinate pattern up to a bijection of coordinates. For a six-transition window starting at $x_r$, assume $r+6\le m$; its five internal counts are $\alpha_{r+1},\ldots,\alpha_{r+5}$. The five-transition row below instead requires $r+5\le m$.

The following statements have completed local refutations and checked actual-snake transfers. They do not assume the collective reference catalogue is refuted.

| Milestone | Direction word | Consequence for the actual counts |
|---|---|---|
| 108–109 | $012304$ | $\alpha_{r+1}\ge3$ or $\alpha_{r+4}\ge3$ or $\alpha_{r+5}\ge4$ |
| 109 | $01234$ | $\alpha_{r+1}\ge2$ or $\alpha_{r+2}\ge6$ or $\alpha_{r+4}\ge3$ |
| 110 | $012340$ | $(\alpha_{r+1},\ldots,\alpha_{r+5})\ne(5,5,2,4,5)$ |
| 111 | $012340$ | $\alpha_{r+2}\ge4$ or $\alpha_{r+3}\ge3$ or $\alpha_{r+4}\ge6$ |

For the first two rows, the omitted counts are unrestricted within their ordinary internal range. The proof first removes unnecessary counter bounds from the local semantic model, checks that the preserved clauses remain consequences of that model, and reuses a checked contradiction. Coordinate normalization and the existing corner-count identities then transfer the result to an arbitrary snake. Milestone 107 also closes the previously missing reference for word $012$ with counts $(1,1)$.

The 111 row is a particularly useful new proposition: simultaneous central caps $(3,2,5)$ are impossible on $012340$, independently of the two outer counts. Its selected certificate contains **2,040 input clauses, 11,711 deductions and 611,907 propagation hints**. Thirteen clauses excluding particular cycles are justified by the snake condition. The independent replay and Lean checks are recorded in the 111 proof summary. The final module proves the actual count restriction and both graph orientations. Reversal must reverse the word and count positions together, since $(3,2,5)$ is asymmetric. This restriction does not subsume the exact tuple excluded in 110, whose second count is 5.

The exact reference catalogue still has **1,378 distinct keys**. The checked recovery now discharges **12 entries**, leaving **1,366** in an equivalent outstanding list. The discharged indices are

$$
0,472,495,535,572,602,619,620,1006,1010,1011,1014.
$$

They consist of $(012;(1,1))$, seven keys for $012304$, and four keys for $01234$. The seven count words are $(2,2,6,2,3)$, $(2,3,6,2,3)$, $(2,4,6,2,3)$, $(2,5,6,2,3)$, $(2,6,4,2,3)$, $(2,6,6,2,2)$ and $(2,6,6,2,3)$. The four are $(1,5,4,2)$, $(1,5,5,1)$, $(1,5,5,2)$ and $(1,5,6,2)$. Here a catalogue symbol 6 denotes the interval $[6,21]$, not exact count 6. `ReferenceCoverage109` proves the twelve entries, the full-union equivalence with the remaining list, and its cardinality. Replace claims that all 1,378 refutations remain open; retain 1,378 wherever it describes the original table or its definition.

## A proved sum bound

The main sum theorem available for insertion is:

> If the six-transition window has direction pattern $012314$ and $\alpha_{r+3}\le2$, then
> $$
> \alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge19.
> $$

The final theorem `ActualSum112.actual_outer_sum` has no unproved local-contradiction or reference-catalogue premise. Its proof normalizes the window to vertices $0,1,3,7,15,13,29$. The counter lists for the four outer centres contain **84 literal occurrences involving 70 distinct literals**. Their multiplicity is essential: the same vertex may contribute to more than one count. The checked counter semantics identifies the number of true literal occurrences with the sum of the four absent-corner counts. Under an outer sum at most 18 and middle count at most 2, the local clauses would therefore be satisfiable, contradicting the checked refutation.

The final selected certificate has **3,306 input clauses, 7,020 deductions and 367,588 propagation hints**. Its active-variable permutation uses **1,718 variables**. The 112 package records 40 successful modules and 20 printed axiom reports. The generic geometric transfer retains a local-contradiction premise; the final theorem supplies that contradiction. Cite the final theorem when stating the result unconditionally for snakes. The package explicitly leaves the graph orientation guards and the new complete graph integration unchecked.

## Combining deficits within one excess budget

Retain the manuscript notation $b_i=\min\{6,\alpha_i\}$ and $\delta_i=\alpha_i-b_i$. Only a short lemma is needed; no new named mathematical objects are required.

For a suffix window with centres $r+4,\ldots,r+8$, let $D_4,D_5,D_2$ denote the positive shortfalls in its clipped outer-four sum, total-five sum and outer-pair sum, respectively, relative to applicable lower bounds on the corresponding actual sums. Those local lower bounds remain explicit hypotheses. For nonnegative integers $a,t$ with $4a+t\le120$,

$$
\max\{aD_4,\min(a,t)D_5,aD_2\}
\le a(\delta_{r+4}+\delta_{r+5}+\delta_{r+7}+\delta_{r+8})
+t\delta_{r+6}.
$$

Each shortfall is bounded by the excess in the same positions. For the total-five shortfall, $\min(a,t)$ is at most each positional coefficient. For the pair shortfall, its two excess terms lie among the four outer terms. Taking the maximum preserves the common upper bound. This is the content of the 112 arithmetic and the 113 pair extension.

Summation over $0\le r<m-8$ gives

$$
\sum_r\max\{aD_4,\min(a,t)D_5,aD_2\}
\le120\sum_{i=0}^{m}\delta_i.
$$

For each fixed shift, the map $r\mapsto r+j$ is injective; hence the four outer contributions and one middle contribution use at most $4a+t$ units of the total excess. Competing deficit credits must be combined by a maximum. Assigning a separate full budget to each family would double count the same excess.

The checked boundary lemma additionally assumes $m\ge8$, endpoint counts at least 4, interior counts at least 1, and adjacent interior count sums at least 4. It yields

$$
\sum_{r=0}^{m-9}b_{r+8}+21\le\sum_{i=0}^{m}b_i.
$$

Consequently any nonnegative credits bounded by the preceding excess sum satisfy

$$
120\sum_{r=0}^{m-9}b_{r+8}+\sum_r\mathrm{credit}_r+2520
\le120\sum_{i=0}^{m}\alpha_i.
$$

This proves safe arithmetic combination. It does not establish any unproved local lower bound used to define a deficit, nor the entire revised graph argument. The checked coefficient domain is the natural numbers; do not silently describe this as a checked theorem for arbitrary real coefficients.

## Statements that still require qualification

| Candidate | Current evidence and required qualification |
|---|---|
| $012034$: central caps $(5,4,5)$ imply $\alpha_{r+1}+\alpha_{r+5}\ge9$ | Native UNSAT without added cuts; the checked geometric transfer still assumes the local contradiction. Both attempted concrete proof constructions timed out. The local witness $(6,5,4,5,3)$ attains pair sum 9, establishing sharpness only within that local model. |
| $012310$: $\sum_{j=1}^{5}\alpha_{r+j}\ge19$ | Complete native refutation independently replayed; concrete Lean semantics checked. The full contradiction batch remains pending. `ActualTotal115` source exists, but its successful receipt was absent at this review. |
| $012345$: $\sum_{j=1}^{5}\alpha_{r+j}\ge23$ | Native UNSAT for total at most 22 after five validated cycle cuts. No checked negative certificate. The longer successful probe does not erase the earlier UNKNOWN attempt. A local forest with counts $(6,3,6,2,6)$ attains total 23; it has six components and is not a complete snake witness. |

The selected 115 proof for $012310$ has 5,114 input clauses, of which 5,067 are used, 287,753 deductions and 16,816,989 hints. These figures describe the selected native replay and export; they do not establish completion of the Lean contradiction. Other exploratory sum rules from 111–112 also remain hypotheses unless separately supplied with a final checked actual-snake theorem.

## Numerical comparisons and limits

The original graph profiles remain $(P,R)=(483,551)$ and $(496,602)$. The later restrictions and deficit weights define separate native experiments. Selected completed-floor means and recorded ranges are:

| Experiment | Mean | Range |
|---|---:|---:|
| 112 expanded seven-rule family | $484$ | $557$ |
| 114 total-five lower bound 19 added | $2424/5$ | $2881/5$ |
| 115 middle-at-most-3 total-five lower bound 22 | $3396/7$ | $4089/7$ |
| 115 universal $012345$ lower bound 21 or 22 | $6309/13$ | $7656/13$ |

The conditional-floor experiments retain mean 496 and range 602. The last completed-floor comparison is $4781536/20303$, whose integer part is 235; the conditional comparison is $551765/2348$, whose integer part is 234. These are native potential checks with attaining cycles under the stated local hypotheses, not new global upper-bound theorems.

The checked arithmetic in 114 makes the remaining requirement precise. For the comparison

$$
(4200d+p)m\le1098960d+8p+R,
$$

excluding $m=235$ requires $227p>111960d+R$, and excluding $m=234$ requires $226p>116160d+R$. Take $d>0$ and $R\ge0$ when interpreting $p/d$ as a slope. Lowering the potential range alone cannot overcome the surviving cycle ceilings in these experiments.

The saved universal-22 completed and conditional cycles have 26 and 6 edges. None of their 64 tested placements has direction pattern $012345$. Raising only that rule's lower bound from 22 to 23 leaves those cycles and their weights unchanged, while removing edges or increasing other weights. Thus the old potential remains valid and the same cycles still attain the mean. This bounded monotonicity argument does not assert a separate full-graph run for lower bound 23 or minimality of the inherited potential range. Conclusions about coefficient ceilings apply only to the fixed tested rule family.

## Recommended manuscript edits and cautions

- Update the abstract, status table, `sec:closure` and `sec:verification`: 1,378 reference keys, 12 checked, 1,366 remaining. Preserve the full-table statement in `prop:reference-union-retention`, adding the checked reduction immediately afterwards.
- Add the local restrictions, proved $012314$ sum theorem and concise certificate proof descriptions in a separate refinements subsection. Keep technical module names and receipt hashes in the verification material rather than the mathematical statements.
- Extend `sec:common-budget` using the existing $\alpha,b,\delta$ notation and the maximum-of-deficits proof. Keep all local sum hypotheses visible.
- Preserve `thm:actual-weight-budget` and the baseline `sec:current-model` argument. The refined native graphs do not automatically inherit its complete interpretation. Keep the existing conditional floor vector and other assumptions of `cor:reference-potential-bounds` unchanged.
- Clearly separate a closed local theorem, a native contradiction, a conditional graph experiment and a complete upper-bound proof. A successful semantic module alone does not prove contradiction. A local forest witness does not show that its counts occur in one global snake.
- Preserve historical appendices as records of their stated models. Do not replace every historical occurrence of 1,378 by 1,366, every mean 483 by a newer restricted-graph mean, or every bucket symbol 6 by an exact count.

No new global numerical bound follows from this review. The saved evidence supports stronger local necessities, a checked shared budget, reduced reference obligations, and more precise limits of the currently tested numerical refinements.
