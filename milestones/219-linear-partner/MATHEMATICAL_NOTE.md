# Round 219: exact limits of the compatible-partner relaxation

The direct target remains a 93-edge induced path starting at endpoint 0 or 78 of the saved 98-edge Q 8 parent and avoiding its other 98 vertices. Joining the two faces would give 192 Q 9 edges. This round gives no such path and no new global bound.

## Result

At both roots, the continuous degree and edge-product formulation admits an exact rational selection of 94 vertices satisfying every simple-cycle occupancy inequality. Adding more inequalities of that cycle form cannot exclude the target in this continuous model. Integrality or other valid inequalities are required.

The source graph has 158 vertices and 337 edges at each root. Vertex variables x, free-endpoint variables e and edge variables y range in[0,1]. The root is selected with degree 1, the odd endpoint variables sum to 1, e<=x, and selected parity totals are equal. At every nonroot vertex, with available degree d and neighbour-selection sum s,

\[
2 x-e\le s\le d-(d-2)x-e.
\]

For Boolean variables this is exactly the conditional selected-degree equation. Edge variables satisfy 0<=y<=x at either endpoint and y>=x_u+x_v-1, forcing y=x_ux_v when x is Boolean. Incident-edge sums give the same selected degrees. Every odd-edge actual partner maps to these necessary rows. No connectivity, integrality, or solver-optimality claim follows for a rational point.

## Exact numerical evidence

| Root | Exact feasible cardinality, all cycles | Exact upper certificate |
|---|---|---|
|0|43286778654/441499285, approximately 98.044957545|49022513/500000=98.045026|
|78|75253867064343/770614508036, approximately 97.654360617|3051701/31250=97.654432|

Vertex-only upper certificates are 108.36883 and 107.110383. The edge formulation is substantially stronger, yet it still permits the target. Root 78's upper certificate implies at most 96 vertices for an actual odd-edge partner, by even integral cardinality; this is 95 edges and has only fixed-parent scope. The old native 97-edge exclusion at root 0 is not recovered by this LP bound.

The upper certificates use integer scaleD=10^6 and weighted rows. Nonnegative weights multiply inequalities; signed weights multiply equalities. With residual r=Dc-A^T Y-E^T Z, box bounds give

\[
D c\cdot z\le b\cdot Y+f\cdot Z+\sum_i\max(r_i,0).
\]

Exact residual compensation makes the statement independent of numerical optimality or dual feasibility. The independent audit reconstructs every model row and recalculates all coefficients, residuals and bounds.

## Certification of every simple-cycle inequality

Write w_u=1-x_u. For each of 337 deleted edges ab, an exact rational potential p satisfies p_a=0, |p_u-p_v|<=w_u+w_v on all other edges, and p_b+w_a+w_b>=2. Summing along the rest of any simple cycle containing ab, then adding the omitted edge, gives 2 sum_C w>=2. Hence sum_C x<=|C|-1 for every simple cycle.

Each certificate has 574 rational coordinates and 337 potential systems. The independent checker verifies all model rows, all box bounds and 113,232 potential-edge inequalities per root. Both minimum cycle costs equal 1, attained on saved squares. This is an exact certificate, distinct from the earlier floating separation report that found no violated cycles at its tolerance.

Mix each rational assignment of cardinalityq>94 with the actual one-edge path[0,2] or[78,14]. Weight 92/(q-2) on the larger assignment gives cardinality 94 exactly. The weights are 10154483555/10600945021 and 70896534739312/73712638048271. Convexity preserves every row and cycle inequality. Both resulting assignments are saved and independently audited. They do not specify Boolean paths.

## Lean and execution scope

Degree 219 passes with four reports: exact integer conditional-degree encoding, Boolean edge-product encoding, residual compensation and the weighted bound with coefficient expansion explicit. CyclePotential 219 passes with four reports: path telescoping, the closing-edge deduction, the twice-counted cycle identity and cycle occupancy. Only standard foundational axioms occur. Numerical coefficient arrays and graph indexing remain independently audited native exact arithmetic; no claim of an end-to-end Lean certificate is made.

The baseline LP, floating cycle separation, and exact basis recovery are terminal with exit 0 and no resource stop. The basis recovery supplies candidates only; the separate rational audit verifies their feasibility without invoking the optimizer or elimination procedure. Exact LP optimality is not asserted. Failed Lean elaboration attempts remain preserved. No software tests were created or run.

## Next deduction

For any vertex subsetU and v inU, an induced path gives

\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]

The selected induced subgraph is a forest. Ifv is selected it is nonempty and has at most one fewer edge than vertices. Ifv is unselected the weaker bound still holds. Put E_t=1 at the root and E_u=e_u elsewhere. Summing the degree equations overU transforms the subset inequality into

\[
\sum_{ab\in\delta(U)}y_{ab}+\sum_{u\in U}E_u\ge 2 x_v.
\]

Thus one minimum-cut calculation for eachv can separate all such subsets: use capacitiesy on the original undirected edges and capacityE_u fromu to a new sink. These inequalities concern all selected edges of a subset, beyond occupancy of individual cycles. Their separation and influence on the bound are not computed in this round. The short counting argument is written; its actual-path Lean integration is pending.

## Maintained state

The interval remains 191<=a(9)<=233. The contributor's 233 final theorem is saved as unconditional, with its independent full rebuild still pending. The 196 conjecture remains open. Remote main and the contributor branch were refreshed; contributor b 0521 e 1 d is unchanged. Earlier parent searches are frozen: case 22 remains 1260 cumulative jobs,11,724,609 nodes,8 pending;27 of 28 six-coordinate choices remain unresolved.

Both existing manuscripts compile and match their E: repository mirrors, with all authors and hypersetup preserved. The goal remains ACTIVE. This round changes the choice of inequalities; it does not meet the pause criterion of a major extremal result or prolonged lack of progress. Contributor work did not cause a pause. No email was sent because no sending tool is available. Full-paper review is due in round 220.
