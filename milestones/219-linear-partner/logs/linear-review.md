# Round 219: independent linear-model and certificate review

The four baseline models and all six saved upper certificates passed independent reconstruction and exact integer/rational arithmetic. This review ran only a saved-record audit using the Python standard library. It did not run an optimizer, proof compiler, search worker, or software tests.

## Necessary constraints

The saved seed is an induced path with 99 distinct vertices in the eight-dimensional cube, starting at 0 and ending at 78. For each root, independently reconstructing the allowed vertices by removing the other 98 seed vertices gives 158 vertices, 337 edges, and 79 vertices of each parity. Every saved square or six-cycle was checked for distinct vertices, cube adjacency, degree two within its selected vertices, and connectivity. There are 279 cycles for root 0 and 274 for root 78.

For an actual odd-edge induced partner rooted at the chosen even root, let \(x_v\) indicate selection and let \(e_v\) indicate the other, odd endpoint. The endpoint-selection, unique-endpoint, root-degree, and parity-balance rows are necessary. With \(s_v\) the sum of selected neighbors and \(d_v\) the available degree, the nonroot rows are

\[
2x_v-e_v\le s_v\le d_v-(d_v-2)x_v-e_v.
\]

For Boolean variables with \(e_v\le x_v\), these impose degree \(2-e_v\) when selected and impose only the available neighbor bounds when unselected. The coefficient \(d_v-2\) is an ordinary signed integer. An actual induced path cannot select every vertex of any saved cycle, so each cycle occupancy row is necessary.

The edge model adds variables \(y_{uv}\) with

\[
y_{uv}\le x_u,\qquad y_{uv}\le x_v,\qquad
y_{uv}\ge x_u+x_v-1.
\]

These force \(y_{uv}=x_ux_v\) for Boolean selections. Their degree equalities therefore preserve every actual partner. The continuous models permit fractional values and do not enforce connectivity. They cover odd-edge partners for this one fixed seed and the two stated roots; they do not cover all nine-dimensional snakes.

Every sparse row, coefficient, variable index, bound, objective coefficient, vertex, edge, and saved cycle was independently reconstructed and compared in order. The integer model sizes and certified upper bounds for the number of selected vertices are:

| Root | Model | Variables | Rows | Exact upper bound |
|---:|---|---:|---:|---:|
| 0 | Vertex | 237 | 676 | \(10836883/100000=108.36883\) |
| 0 | Edge | 574 | 1845 | \(49022513/500000=98.045026\) |
| 78 | Vertex | 237 | 671 | \(107110383/1000000=107.110383\) |
| 78 | Edge | 574 | 1840 | \(3051701/31250=97.654432\) |

All four bounds exceed 94. The edge-model bounds, together with even integral cardinality of an odd-edge path, imply at most 98 selected vertices for root 0 and 96 for root 78. Neither excludes the requested 94-vertex partner.

## Exact certificate argument

Write the saved objective as \(c\cdot z\). Each inequality row \(a_j\cdot z\le b_j\) receives an integer weight \(w_j\ge0\); equality rows may receive signed integer weights. For the positive scale \(S=10^6\), define the residual coefficients solely for this calculation by

\[
r_i=Sc_i-\sum_jw_ja_{ji}.
\]

Using the saved bounds \(0\le z_i\le1\) gives

\[
Sc\cdot z
\le\sum_jw_jb_j+\sum_i\max(r_i,0).
\]

The audit recomputed every residual, positive part, weighted right-hand side, numerator, and reduced rational upper bound. It checked nonnegative inequality weights, signed equality weights, model hashes, and the correspondence between weights and the saved rounded numerical duals. The certificate argument requires neither numerical dual feasibility nor the solver's optimality claim.

No exact primal certificate was saved for any of the four baseline models. Consequently this audit establishes no exact feasible objective of at least 94 and no impossibility of improving the upper certificate within these constraints. The reported floating-point optima remain numerical observations.

## Cycle-separation extension

Both saved cycle-extension models have precisely the same variables, bounds, objective, rows, vertices, edges, and initial cycles as their corresponding baseline edge models. They added zero rows. Their independent exact upper-certificate recomputations return the same two edge bounds above. The recorded absence of additional violations is a floating-tolerance observation; this audit does not claim exhaustive exact separation over all cycles. The extension execution record is terminal and its pinned source/input hashes match.

## Execution and evidence limits

The baseline execution record reports normal exit 0, no resource stop, 2.609 seconds, maximum sampled private memory 21,069,824 bytes, and minimum sampled free memory 1,017,413,632 bytes. The source/input pins, saved stdout and stderr hashes, summary hash, four thread limits, and sampled resource conditions agree with the record. Sampling does not certify an unobserved instantaneous memory maximum.

The wrapper and model source have no identified soundness defect affecting accepted certificates. A nonoptimal solver return currently stops at an assertion without saving a separate numerical status result. Its saved model and failed execution would remain evidence of an unfinished computation; it could not justify an exclusion.

The audit is a native exact-arithmetic review of these saved models and certificates. It is not a Lean proof of the entire model-generation or certificate-checking procedure, an exact verification of numerical optimality, an actual partner construction, or a global upper-bound improvement.

## Source pins

- `scripts/linear_partner.py`: `4be866eb9b8764a5f756d36e1876ef866fa93fed0dd64c68dd445dea12c794fb`
- `scripts/run_lp.py`: `4ccb2d8bda3c08c0d0ae1da928e7b32c1fbf4e2cff3ea6e05436b95c8029b17b`
- `scripts/audit_linear.py`: `2292b0d548a08c08c7c7ddf99798a1fe637214e164e4471dbb1707f0d1a5bcd2`
- `data/seed98.json`: `2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5`
- `data/complement-graph.json`: `6af4976a40d897be2c43790c75b66fac0473f0a97226d3fdb106140744a94c82`
- `data/lp-summary.json`: `5749cfe011f6e22644c6b6a4f95381fb9c2b8820790fc2f5da078238c22db3f4`
- `data/lp-execution.json`: `f7ddd8bcd65844834909c720292b0caccf5c359488ff916f64495962053f045d`

The per-model, certificate, and result hashes are recorded in `data/linear-audit.json`. These baseline audit files are frozen; any subsequent exact primal belongs to a separate addendum.
