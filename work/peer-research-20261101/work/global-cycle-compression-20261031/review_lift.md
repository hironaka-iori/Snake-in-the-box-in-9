# Independent history-lift review — 2026-10-31

Verdict: PASS for the reviewed standard-library transducer and static NPZ-adapter logic, with NumPy execution explicitly BLOCKED by Windows application control. The real multi-million-edge NPZ was not loaded or transformed here, and no new global bound is claimed. Source hashes are recorded in `review_lift.json`.

## Exact language and off-by-one

The four marked source edge IDs form one directed four-cycle on four distinct vertices, one marked outgoing edge at each of these vertices. Consequently every contiguous run consisting only of marked edges follows that cycle, including one of its four cyclic phases. For this specific marked subgraph, forbidding seven consecutive marked edges is equivalent to forbidding the four proven seven-ID patterns.

The split state (v,r) records the consecutive marked run length r. Every unmarked edge resets r to zero. A marked edge increments it. At r=6 the next marked edge is absent. Thus six marked edges remain legal and the seventh is rejected. Seven is not counted as the seventh *visit* to a state, nor as seven complete tours. The meaning depends on the marked subgraph; `lift_graph` is a general membership-run transducer and does not independently prove that an arbitrary supplied ID set is a four-cycle. Its default max_run=6 implements the currently proved exclusion.

Starting a genuine source walk from (start,0) yields exactly one lifted walk until a forbidden history occurs. Conversely every lifted walk projects to a source walk with the original edge weights and no seven-edge marked run. Initial nonzero counter states may impose a stricter initial history, but cannot admit an invalid seven-edge pattern. They do not remove the valid zero-counter representation of any accepted source walk.

Only the four special vertices require extra counters. Non-special vertices always have counter zero, since every marked edge's endpoint is special. Four vertices times six additional run states give 24 extra states. The original base state IDs in the NPZ adapter represent counter zero and remain unchanged.

## Shared states and multiple outgoing edges

The adapter changes only the marked original row destinations to target counter one; unmarked base rows retain their destinations. Each extra counter source receives a copy of EVERY original outgoing edge. Unmarked copies, including self loops and parallel edges with different row IDs, reset to the original destination's base state. Marked copies advance to the next counter, except those at run six. Therefore leaving the cycle at a shared graph state is preserved; this is not a deletion of the whole source SCC or of individual marked source edges.

Static inspection confirms that all additional edge attributes are copied using their original row indices, and the projection array returns precisely those row indices. U and V are then replaced by the required lifted endpoints. The copied weight is unchanged. Hash verification is enabled in the actual CLI, and each marked row is additionally bound to its declared u/v/weight and cycle order. The original source arrays are not mutated.

An already valid mean480 potential can be pulled back along state projection, retaining range578: every lifted edge has exactly one original edge with unchanged weight, so its old potential inequality remains true. This is conditional on the original potential certificate being valid. It establishes no improvement above480. Other mean480 cycles can remain, as the author's toy counterexample correctly demonstrates. A new strict mean/range certificate is still required for a numerical improvement.

## Independent executable controls

`review_lift_stdlib.py` constructs a six-node, eleven-edge graph: the marked four-cycle plus unmarked branching, an unmarked self loop, and an unmarked edge parallel to a marked edge. It checks all 15,840 rooted source walks of depth at most ten against the FOUR EXPLICIT forbidden seven-ID patterns, rather than relying on the implementation's membership counter as its oracle. For every source state/counter and outgoing source edge, it separately verifies the expected unique copied target or exact r=6 omission (65 checks). Projection endpoints and weights are checked. The lifted graph has 30 states and 61 edges. All checks PASS.

`review_lift.py` is a prepared NumPy execution test, but its import failed because Windows application control blocked NumPy's compiled DLL. It did not execute `transform`, and must not be listed as a passed NPZ test. No bypass was attempted. `review_lift.json` explicitly records the blocked scope and lack of a real NPZ run.

## Defensive checks before broad reuse

The actual frozen source cycle has positive row IDs, valid distinct nodes, and sufficient integer ID capacity. For arbitrary external inputs, explicitly reject negative/out-of-range edge IDs, endpoints outside 0..N-1, multidimensional/noninteger endpoint arrays, and endpoint dtypes unable to represent N+23; otherwise negative Python indexing or narrow integer overflow could silently misapply a synthetic case. Likewise require nonnegative integral max_run in the generic API. These are input-hardening recommendations; no counterexample was found for the declared frozen upstream cycle and correctly hashed arrays.

The implementation uses asserts for cycle and row bindings; run without Python -O, or replace these guards with explicit exceptions. The real model transform, complete lifted-model mean, automaton-to-arbitrary-snake bridge, endpoint constants, and resulting global235 exclusion remain UNVERIFIED by this review. The report's `new_global_bound: null` and `full_model_mean_recomputed: false` are the appropriate labels.
