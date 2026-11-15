# Round 220: independent subset and flow certificate audit

The exact saved-data audit passed for both roots. Each new model has 25 correctly encoded subset inequalities, and both have exact rational feasible points satisfying every simple-cycle occupancy inequality and every inequality in the stated subset family. Their checked convex mixtures have objective exactly 94. Consequently these continuous constraints, even taken in full, cannot exclude the 94-vertex target.

This audit used only saved records and standard-library integer/rational arithmetic. No optimizer, compiler, search worker, software tests, or repeated basis elimination were run. The manuscript review and all producer evidence remain unchanged.

## Model and added-row validity

The original round-219 edge model hashes and prior audit receipts were checked. Every original row, variable, bound, objective coefficient, vertex, edge and static cycle is unchanged. The two models still have 574 variables, 158 graph vertices and 337 undirected graph edges. They now contain 1,870 and 1,865 rows respectively.

For each saved subset \(U\) and distinguished vertex \(v\in U\), all coefficients and indices of the added row were independently reconstructed. Its inequality is

\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]

The audit checks the 25 distinct subset/vertex keys, membership, exact appended row indices, names, coefficients, sense, right-hand side, and iteration/count consistency. It does not reconstruct the floating solution at every intermediate discovery iteration; that is unnecessary for validity of an added row.

For a Boolean induced path, the selected vertices in \(U\) induce a forest. If \(v\) is selected, this nonempty forest has at least one fewer edge than vertices; if \(v\) is unselected, the weaker edge-versus-vertex bound suffices. The product constraints identify the selected edges. Thus every added inequality is necessary for an actual partner. No assumption that \(U\) is connected is used.

## Exact upper and lower certificates

| Root | Exact certified upper bound | Exact feasible objective |
|---:|---:|---:|
| 0 | \(97840921/10^6=97.840921\) | \(22588258102073/230867380070\approx97.8408387327\) |
| 78 | \(97359759/10^6=97.359759\) | \(3545809907526/36419686519\approx97.3597042269\) |

All upper-certificate integer multipliers, nonnegative inequality weights, signed equality weights, coefficient residuals, positive residual parts and resulting bounds were recomputed. The variable interval from 0 to 1 justifies the residual correction. This gives exact upper bounds without assuming numerical dual feasibility or numerical optimality.

All 574 coordinate bounds and every original and added row were checked exactly for the new rational points. The points have 414 and 407 nonintegral coordinates. The exact gaps between upper certificate and feasible objective are

\[
\frac{1899283284447}{23086738007000000},\qquad
\frac{1994819388921}{36419686519000000}.
\]

These positive gaps do not certify the exact optimum. The upper bounds imply at most 96 vertices for a Boolean odd-edge partner at either root, using its even cardinality. They leave the requested 94-vertex target possible within this necessary model.

## The old points violate valid subset inequalities

Each saved round-219 source point was hash-matched to its frozen audit and evaluated against every recorded violating subset. All four points still satisfy their original model rows. Their recorded positive subset violations are exact:

| Root | Old point | Checked witnesses | Largest recorded violation |
|---:|---|---:|---:|
| 0 | Original rational point | 22 | \(280247959/1765997140\) |
| 0 | Cardinality-94 mixture | 22 | \(6445703057/42403780084\) |
| 78 | Original rational point | 23 | \(519838852993/1541229016072\) |
| 78 | Cardinality-94 mixture | 23 | \(23912587237678/73712638048271\) |

These are counts of saved subset/vertex witnesses, not an enumeration of all violating subsets. For every witness the audit independently evaluated internal-edge mass, selected-vertex mass, boundary-edge mass and endpoint mass, checking both the stated violation and its degree-sum identity. No minimum-cut or maximum-flow optimality claim is needed to establish these violations.

## All simple-cycle inequalities

For each root, all 337 saved edge-deleted potential systems were checked, with 113,232 exact potential inequalities. Every target is independently reachable after its designated edge is deleted. Each potential has zero value at its source, respects the edge lengths \((1-x_u)+(1-x_v)\), and gives a closing-cycle lower bound at least one.

Telescoping along a simple cycle with one edge removed therefore proves
\(\sum_{u\in C}(1-x_u)\ge1\) for every simple cycle \(C\).
The minimum is attained at one: a saved square on \(\{20,22,84,86\}\) does so for root 0, and one on \(\{4,6,20,22\}\) does so for root 78. The argument does not rely on the floating separator's stopping tolerance or on shortest-path optimality.

## All subset inequalities from feasible flows

For each root, the audit reconstructs the complete directed network. Each undirected graph edge receives two directed arcs of capacity \(Dy_{uv}\). Every graph vertex has one arc to the sink: capacity \(D\) at the fixed root, \(De_u\) at each odd endpoint variable, and zero at the other vertices. There are exactly 832 directed arcs. The common integer scales are 461,734,760,140 and 36,419,686,519.

The audit checks all 158 local degree identities, including the root identity. If \(E_u\) denotes endpoint mass, with \(E_{\mathrm{root}}=1\), these are

\[
\sum_{w\sim u}y_{uw}=2x_u-E_u.
\]

Every graph vertex has its own saved feasible source-to-sink flow. For all 158 flows per root, the audit checks every arc's nonnegative amount and capacity bound, zero conservation error at all other vertices, equal source supply and sink receipt, and supply at least \(2Dx_v\). This is 131,456 exact arc-capacity checks per root. Zero-coordinate sources are included, with a valid zero flow. Duplicate or invalid sparse arc indices are rejected. Maximum-flow optimality is neither checked nor needed.

For an arbitrary subset \(U\) containing the flow source \(v\), sum conservation over \(U\). Internal flows cancel and incoming flow is nonnegative, so the outward cut capacity is at least the source supply. After division by \(D\),

\[
2x_v\le
\sum_{ab\in\delta(U)}y_{ab}+\sum_{u\in U}E_u.
\]

Summing the checked degree identities over the same subset gives

\[
2\sum_{u\in U}x_u
=2\sum_{ab\in E(U)}y_{ab}
 +\sum_{ab\in\delta(U)}y_{ab}+\sum_{u\in U}E_u.
\]

Combining these proves the required subset inequality for every \(U\) and every \(v\in U\). Thus the exact flows certify the entire family, beyond the 25 explicitly added rows. This is independent of numerical separation completeness.

## Exact cardinality 94

Both target certificates combine the new rational point with an actual one-edge path: \([0,2]\) or \([78,14]\). Their complete Boolean encodings were independently reconstructed and all saved rows and bounds checked. The mixing weights are

\[
\frac{21239798966440}{22126523341933},\qquad
\frac{837652789937}{868242633622}.
\]

They equal \(92/(Q-2)\), where \(Q\) is the corresponding rational objective, and lie strictly between zero and one. Every mixed coordinate was recomputed; every model row and bound was checked again; each objective is exactly 94. The mixtures have 423 and 427 nonintegral coordinates.

The actual one-edge paths satisfy all simple-cycle and subset inequalities. Both families are linear, so their convex mixtures with the fully certified rational points satisfy both families as well. This establishes exact continuous feasibility even after adding the cardinality equality. It does not establish a Boolean path or connectivity of a selected vertex set.

## Execution provenance and Lean scope

All three producer execution records are terminal, with exit 0 and no stop reason. Source/input pins, stdout/stderr hashes, summary hashes, thread settings and saved resource conditions match. Recorded elapsed times are 3.156 seconds for subset separation, 2.672 seconds for rational reconstruction and 0.797 seconds for feasible-flow generation. Their maximum sampled private memories are 31,248,384, 44,670,976 and 30,027,776 bytes respectively. These are sampled observations.

The inspected `Forest220.lean` source separately supplies the generic actual-path edge-counting statement and an integer degree-boundary equivalence. Its compiler verification belongs to the separate proof record. This audit does not claim that the concrete sparse arrays, all rational flow data, the all-cycle argument, and the complete model interpretation have been assembled into one Lean theorem. The native exact evidence and the generic proof bridge must retain that distinction.

No numerical global snake bound or new construction follows. The useful result is an exact limitation of the specified fixed-parent continuous formulation after both complete families of inequalities have been imposed.

The complete source and evidence hash map is in `data/forest-audit.json`. The unchanged manuscript-review hash is `c7492e5b4ee38feedd4fb4843aa9a93f31f16b6fe328da02820720b5e4b61378`.
