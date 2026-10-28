# Milestone 59: extending the forced-empty-square window

This round tests one additional transition in the empty-square calculation. The longer segment gives stronger local inequalities, but it does not lower the integer upper bound. The contributor-checked global interval remains **191 <= a(9) <= 235**, and the exact optimum remains unresolved.

## Nine-transition geometry

For a consecutive segment W=(x_0,...,x_9), every internal vertex x_1,...,x_8 already has two selected neighbours. Let D consist of their remaining neighbours. All vertices of D are absent from the snake. As in milestone 58, let U be the complement of D and calculate the corner share using U as a superset of the actual selected set. Monotonicity gives

\[
L_9(W):=\sum_{i=4}^{8}\sigma_U(x_i)
\le\sum_{i=4}^{8}\sigma_S(x_i).
\]

The charged centres are the same five centres used by the eight-transition suffix. The larger forced-absence set therefore gives a lower bound at least as strong as the earlier geometric bound.

There are 505 canonical induced nine-transition shapes. Of these, 357 have positive geometric credit, 231 improve on the eight-transition suffix, and the largest credit is 54. The separate verifier enumerates every shape and all 4,608 cube faces. It checks forced absence, the empty-square counts, the denominator upper bounds and every share summand.

The Lean catalogue checks each positive shape and transports its inequality to every matching segment of an arbitrary snake. The proof uses the same degree and share-monotonicity argument as milestone 58. A checked binary-mask representation accelerates the finite calculations; the mask condition proves that every vertex it excludes belongs to D. It introduces no numerical solver premise. Successful build coverage and theorem dependencies are recorded in `data/lean-audit.json`.

## Enlarged finite model

The state retains eight direction labels up to relabelling and five truncated singleton counts. A transition has nine directions and six count symbols, referring to internal positions 3,...,8. It inherits the prior restrictions from its eight-transition suffix. Its source state stores the first five counts and its target state stores the last five. Symbol 6 continues to mean the interval [6,21].

The model has 1,026,432 states and 11,594,078 transitions. Two versions separate the effect of retaining more directions from the new geometric credits:

| Model | Exact normalized mean | Potential range | Attaining cycle length | Conditional integer bound |
|---|---:|---:|---:|---:|
| Longer direction memory, old credits | 617/150 | 3,122 | 20 | 235 |
| Longer memory and new credits | 3297/800 | 12,101 | 20 | 235 |

The new credits strengthen 5,308,975 transitions. The separate verifier checks the complete suffix lift, every edge potential inequality and the attaining cycles. The new cycle has 51 recorded share units, compared with 32 in the lifted old model. The mean improvement is 19/2400 in normalized units.

These are exact minima of the recorded finite models. The models inherit numerical exclusions and share rules whose proof replay remains incomplete. The complete graph-to-snake assembly is also pending. No new global upper bound follows solely from these computations.

## Boundary and overlap accounting

Five consecutive charged centres have overlap multiplicity at most five, regardless of their fixed offset inside the longer segment. Lean checks this offset-independent summation inequality.

If m is the number of edges, a nine-transition window contributes at each of m-8 starting positions. The entering-count sum omits seven internal vertices and the two endpoints. The established individual lower bounds give an omitted count contribution of at least 7+4+4=15. Thus, writing W for the total model weight and G=24T+Sigma,

\[
W+1800\le5G,
\qquad G+840(m+1)\le221136,
\qquad W+4200m\le1099680.
\]

For an edge potential with mean p/d and range R,

\[
p(m-8)\le dW+R
\quad\Longrightarrow\quad
(p+4200d)m\le1099680d+8p+R.
\]

The extended model has p=9891, d=20 and R=12101, giving the conditional estimate

\[
m\le\frac{22\,084\,829}{93\,891}\approx235.218.
\]

Lean checks the overlap inequality, the aggregate arithmetic, the potential consequence and the conditional integer bound 235. The extra omitted singleton contribution is retained; using the old constant 1099800 here would unnecessarily weaken the result.

The stronger mean does not yet compensate fully for the longer window's boundary cost. Milestone 58's conditional estimate is approximately 235.188, so that earlier estimate remains the better of the two.

## What this rules out and what remains useful

Improving the potential range alone cannot reach 234 in this model. Even with range zero, excluding m=235 requires

\[
\mu>\frac{112680}{227},
\]

whereas the attaining cycle gives mu=9891/20. Lean checks the resulting arithmetic obstruction. Additional valid restrictions or stronger share credits are required.

A limited probe moves the charged centres from positions 4,...,8 to positions 3,...,7 and reevaluates both the geometric and inherited count-specific shares on the saved cycle. Its mean remains 9891/20. This cycle therefore also prevents that simple recentering from reaching 234 under the same accounting. No complete centred-model minimum is asserted.

The bank check verifies 131 stored snakes and 47,946 oriented nine-transition windows. Of these, 36,368 receive positive credit; 271 shapes occur, and the smallest observed actual-share excess above the bound is 128. These examples support consistency; the universal geometric inequalities are established by the Lean proofs.

The next useful direction is to strengthen the forced-absence information on the surviving cycle, for example by checking ten-transition extensions. The unchanged mean in the recentering probe gives a reason to prioritize genuinely additional geometric information over another rearrangement of the same nine-transition charge.

## Files and reproduction

- `scripts/extend.py`: enumerate the geometry and construct both suffix-lift models.
- `scripts/analyze.py`: find attaining cycles and check complete integer potentials, with the nine-transition boundary correction.
- `scripts/prepare_geometry.py`, `replay.py --resume`, `audit_lean.py`: generate, check and audit the geometric catalogue.
- `scripts/verify.py`: separate geometry, graph, potential, bank and centering checks.
- `scripts/centering_probe.py`: evaluate the alternative centre placement on the saved cycle.
- `data/verification.json`, `data/lean-audit.json`: computational and Lean evidence with explicit scopes.

This is research round 3 of 10 after manuscript revision 56. The paper and its open editor mirror remain unchanged and synchronized. The next scheduled full revision is milestone 66. The compilation limitation recorded in milestone 56 remains unresolved.
