# Meaning and use of the proposed share-18 lemma

Read-only mathematical audit for the later manuscript revision. No compiler, solver, graph worker, paper edit or accepted-source edit was run. The review uses the current paper, including its milestone-156 discussion, at SHA-256 `e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb`. It does not certify completion of the share-18 refutation or the final actual-snake composition.

## 1. What the integer 18 measures

Use the existing paper notation: $S=V(P)$, $P=(x_0,\ldots,x_m)$, $v=m+1$, and

\[
e(q)=\#\{\text{empty coordinate squares containing }q\},\qquad
d(q)=|N(q)\cap S|,\qquad
\sigma_{12}(x)=\sum_{q\sim x}\left\lfloor\frac{12e(q)}{d(q)}\right\rfloor.
\]

`LocalWindowShareModel.emptyCount` counts the 36 possible coordinate pairs at $q$, retaining a pair exactly when all four corners are outside $S$. `cnt S (nbrs q)` is the number of selected neighbours of $q$. It is not the degree of $q$ in the induced path when $q\notin S$. `shareLocal` takes the integer quotient after multiplying this entire empty-square count by 12. `coreShare 12 p k` evaluates the same quantity at $x_k$. `CoreShareBudget.shareN_eq_coreShare` identifies it exactly with the global share, so there is no additional factor in the local-to-global transfer.

For selected $x$, every neighbouring $q$ has $d(q)\ge1$. A selected $q$ has $e(q)=0$, so the two selected neighbours of each internal centre contribute zero. An external neighbour may occur in the sums of several centres. This repetition is intentional: each of its $d(q)$ selected neighbours receives the same integer quotient.

The intended local conclusion is

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge18.
\]

It concerns the total allocated integer share received by five internal vertices. It gives neither 18 empty squares nor a bound of 18 at each centre. A single empty square has four corners, each of which may distribute its contribution to selected neighbours.

Division by 12 has the precise interpretation

\[
\frac32\le\frac1{12}\sum_{j=1}^{5}\sigma_{12}(x_{r+j})
\le\sum_{j=1}^{5}\sum_{q\sim x_{r+j}}\frac{e(q)}{d(q)}.
\]

Thus 18 implies at least $3/2$ units of the unrounded allocation of empty-square corner incidences to these five centres. Equality with the unrounded allocation is not justified in general: the floor occurs in each neighbour term, and resolution 12 does not clear every possible denominator. The phrase “1.5 empty squares” would lose both this rounding qualification and the factor of four from square corners. The integer formulation is the one used by the certificate and should remain the primary statement.

## 2. Shape, counts, endpoints and proof status

The source `Share144.Geometry.share_bound` has exactly these geometric hypotheses:

- $P$ is an induced path in $Q_9$, with $m$ edges.
- $r+6\le m$.
- $a,b,c,d,e$ are distinct coordinate labels below 9.
- Its six directions at $r,\ldots,r+5$ are $(a,b,c,a,d,e)$, the canonical shape $012034$.

The reverse source uses $(e,d,a,c,b,a)$ and the same five-centre sum. The canonical window is $[0,1,3,7,6,14,30]$. All five stored count intervals are $[0,21]$, with resolution 12 and forbidden cap 17. The inequality is obtained by refuting a sum at most 17, then using integrality. The bound 21 is automatic at internal centres: the two incident path directions leave seven free coordinates and at most $\binom72=21$ singleton squares. Consequently the intended universal share-18 theorem has no additional singleton-count hypothesis. It would cover, in particular, the narrower selected context $(3,[6,21],4,3,[6,21])$.

The five charged vertices are internal, while the first or last vertex of the seven-vertex segment may be a global endpoint. There is no hypothesis excluding endpoints from a surrounding ball, requiring a particular endpoint distance, or imposing parity. The local axioms do retain necessary properties of an actual nontrivial path: selected degrees between one and two, absence of selected cycles, and at most two endpoint vertices. These restrictions cannot be dropped when interpreting the finite refutation.

The accepted generic `refuted_share_bridge` transfers a `RefutedShare` result to this actual-snake inequality. Milestone 159's saved semantics completion establishes that the local axioms with cap 17 produce a satisfying assignment of the fixed CNF; that receipt explicitly records `complete_contradiction_replay=false` and `actual_snake_share18_theorem=false`. The full replay and subsequent refutation/geometry/reversal composition remain separate acceptance steps. The presence of `Geometry.lean` alone does not discharge them.

## 3. Entry into the global charge and the finite comparison

The paper's exact loss identity and charge definition are

\[
\Sigma+\sum_q r_{12}(q)=48s_0,\qquad
G_{12}=24T+\Sigma,\qquad \Sigma=\sum_{x\in S}\sigma_{12}(x).
\]

Together with $T+2s_0+35v=9214$, these give

\[
G_{12}+840v+\sum_q r_{12}(q)=221136,
\qquad G_{12}+840v\le221136.
\]

Here $r_{12}(q)$ is already defined in the paper. The charge $G_{12}/24\le T+2s_0$ gives the scale relative to the square identity. An integer share contribution of 18 enters $G_{12}$ as 18, before accounting for overlap. It must not be divided by 12 inside the existing integer graph weights.

For nine-direction contexts, the graph charges the last five internal positions $r+4,\ldots,r+8$. A six-direction suffix $012034$ would permit $L_r=18$ on precisely that five-centre window. Distinct starts charge any path position at most five times, yielding $\sum_r L_r\le5\Sigma$. Several certified lower bounds on the same sum can be combined by their maximum. Adding prefix and suffix bounds for overlapping copies requires a proved capacity estimate; their numerical values alone do not justify addition.

The weight is $120b_{r+8}+L_r$, where $120=5\cdot24$. The omitted singleton positions contribute at least 21: four from each endpoint, four from each of three disjoint adjacent internal pairs, and one from the seventh internal position. Hence

\[
W+2520\le5G_{12},\qquad
W+4200m\le1098960.
\]

The constants follow directly: $2520=120\cdot21$, $4200=5\cdot840$, and $1098960=5\cdot221136-4200-2520$. `GlobalCharge98.actual_total_weight_budget` states this last inequality for `Snake m`, with a per-window share premise. The theorem does not silently replace $m$ by $v$.

A potential with mean $\mu$ and range $R$ on the $m-8$ transitions gives $\mu(m-8)\le W+R$. If each recorded low-pair occurrence receives extra weight $C\ge0$, at most 24 such occurrences give a total allowance $24C$. Subject to the relevant graph coverage, weight, occurrence and potential premises,

\[
(4200+\mu)m\le1098960+8\mu+24C+R.
\]

The resulting ratio bounds **edges** $m$. Its being strictly below 235 is sufficient for $m\le234$, because $m$ is an integer. Requiring the ratio to be below 234 would be unnecessarily strong for that target; it would imply $m\le233$.

For $\mu=496,C=0,R=602$,

\[
4696m\le1103530,
\qquad \frac{1103530}{4696}=235-\frac{15}{2348},
\qquad 4696\cdot235-1103530=30.
\]

Therefore this comparison gives conditional 234, although the rational comparison remains greater than 234. The checked arithmetic in `RangeObstruction156` establishes a lower limit on the comparison within its specified finite graph, rather than a lower bound on the maximum snake length. `PotentialAssembly98.conditional_upper234` independently makes the edge conclusion explicit as `p : Snake m` implies `m ≤ 234`, retaining the local-share, reference-refutation and complete-potential premises. Completing the share-18 lemma discharges one local premise; it does not discharge the other premises or create a new unconditional bound.

For completeness, the stronger charge targets have exactly one unit of separation at the first forbidden vertex count:

| Target | First forbidden $v$ | Proposed lower bound on $G_{12}$ | Global upper bound $221136-840v$ |
|---|---:|---:|---:|
| $a(9)\le230$, from $G_{12}\ge114v-191$ | 232 | 26257 | 26256 |
| $a(9)\le231$, from $G_{12}\ge114v-1145$ | 233 | 25417 | 25416 |

The lower bound increases and the upper bound decreases with $v$, excluding every larger $v$ as well. The resulting vertex bounds are 231 and 232; subtracting one gives edge bounds 230 and 231. `SharePacking.upper230_of_charge` and `upper231_of_charge` explicitly use $m+1$ in the premise and conclude the corresponding bound on $m$. These hypotheses remain unproved for arbitrary snakes.

## 4. Optional retention of the exact remainder

The source takes `floor(12 * emptyAt / selDeg)`, not `emptyAt * floor(12 / selDeg)`. This order matters.

If $e(q)>0$, one empty square through $q$ supplies two unselected neighbours, so $d(q)\le7$. More generally $e(q)\le\binom{9-d(q)}2$: both face directions must lead to unselected neighbours. Thus degree seven permits $e(q)\le1$, and degree five permits $e(q)\le6$. Since $1,2,3,4,6$ divide 12, the exact identity simplifies to

\[
\sum_q r_{12}(q)
=12\sum_{d(q)=0}e(q)
+\sum_{d(q)=5}\bigl(2e(q)\bmod5\bigr)
+5\sum_{d(q)=7}e(q).
\]

This is a mathematical deduction from the inspected definitions; it was not newly checked in Lean during this audit. The paper currently states the general remainder identity, without this degree decomposition.

Replacing the middle term by $2\sum_{d(q)=5}e(q)$ is false. A small induced path with vertices $[1,3,2,6,4,12,8,24,16]$ has, at $q=0$, five selected neighbours and six empty squares. Its actual remainder is $72\bmod5=2$; rounding separately for each of those six face incidences would give 12. The 36 vertex-pair tests for this nine-vertex witness and its local counts were checked by direct finite arithmetic in this audit. This is a counterexample to that simplification, with no extremal claim.

Retaining the exact loss in the existing aggregation would give

\[
W+4200m\le1098960-5\sum_q r_{12}(q),
\]

and subtract the same term from the numerator of the edge comparison. No positive lower bound for this sum has been established here. The identity alone therefore does not improve the numerical bound.

## 5. Editorial recommendations

1. State the local result with the existing $\sigma_{12}$ notation and all five centres explicitly. Explain in one sentence that it allocates rounded empty-square corner incidence.
2. If giving $18/12=3/2$, say that it is a lower estimate of the unrounded allocation. Avoid calling it a count of distinct squares.
3. Place the scale statement $G_{12}=24T+\Sigma$ and the fivefold overlap statement immediately before using the local bound in graph weights.
4. Label the potential ratio as an upper bound for edge length $m$. State explicitly that a ratio below 235 implies the integer bound 234.
5. Preserve the proof-status distinction between checked CNF semantics, complete contradiction replay, actual-snake composition, and global graph coverage. No new definition is needed for any of these explanations.

## Inspected source pins

Paths below are relative to `E:\Snake-in-a-box`. Hashes pin the audit inputs, not a fresh rebuild.

| File | SHA-256 |
|---|---|
| `paper/snake9_research.tex` | `e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb` |
| `milestones/147-countfree-clause-semantics/lean/LocalWindowModel.lean` | `5c374d6b74cbed0ebb91f93e53de21f6e33a85f64532dca6c09f7cefe3a6a8a0` |
| `milestones/147-countfree-clause-semantics/lean/LocalWindowShareModel.lean` | `3a9210925cbd9432b5c1022c9cd85abff80d8ee008ea8efb53affd75c931f3a3` |
| `milestones/148-actual-snake-share-transfer/lean/LocalWindowShareBridge.lean` | `8b2d06a67664f7d9ded4d0b3422e8cf73c151caed2a0cc08772ec74cf7d59ca8` |
| `milestones/148-actual-snake-share-transfer/data/LocalWindowShareBridge-audit.json` | `9b8e7298a666664f5c1eb486d6598d3766cf7f055ee08aecf51c600dcd88f16c` |
| `milestones/144-countfree-share18/lean/LocalWindowCnf/ShareWindow144.lean` | `1fa19f9fa0fe21ef77240a2572eee3a8dfd8c886cfd8359341415bd59b0320ad` |
| `milestones/144-countfree-share18/lean/Share144/Geometry.lean` | `5358fed5cabd2d1161f1268805f534494bdd6341cba8ffd9009e834ebaa6bac0` |
| `milestones/144-countfree-share18/lean/Share144/Reversal.lean` | `7552de4acedefa31a48cc888f989ffef3734fb48ebdb99bc661a2707163cf26e` |
| `milestones/73-countfree-share-catalogue/bridge/upstream/ShareCharge.lean` | `0cce56ffd22c51a684952427885d98c218e19b48f5f5ffe56399f851407ca26d` |
| `milestones/73-countfree-share-catalogue/bridge/lean/CoreShareBudget.lean` | `81ccb6a86bb022c4acc6e5a15f09e5960caa5e0256ea4c6771830f9920344f0a` |
| `milestones/27-empty-square-packing/lean/SharePacking.lean` | `b8568f93b327ee3f2dc8403ce1cf9f43c18d5a4b9a637b6a97ebbbf23b82e022` |
| `milestones/67-critical-family-charge/lean/BoundaryCharge.lean` | `52d8e21be70a6ea34d98f140eef9e123b41b532f34dbe838cdea82f94991e52e` |
| `milestones/98-concrete-weight-integration/lean/GlobalCharge98.lean` | `3bce11e1fcbb19c51385c0def17617f3ffc87ea4c23ed16c95fef3fee10cdc29` |
| `milestones/98-concrete-weight-integration/lean/PotentialAssembly98.lean` | `bd5bceccfeda6c7b5d2a602dac0326508dfa63ceb2f1a58d69ff99778aa18eb4` |
| `milestones/156-potential-range-and-paper/lean/RangeObstruction156.lean` | `7b12e3e578e0f532da8c31b42f27bcf7c82a18a921fc9970e72bede126a5863e` |
| `milestones/156-potential-range-and-paper/data/range-lean-check.json` | `ebed3431c6d4ad77872a42c9b813f22da82f2cdd32b72a7fbaef26f3b3b36c8b` |
| `milestones/159-share18-proof-continuation/data/semantics-completion.json` | `3e467570d8987e7fc0f72b5d96e0e35bc6f8a4101a1d583e49af1b15b0c631d9` |
