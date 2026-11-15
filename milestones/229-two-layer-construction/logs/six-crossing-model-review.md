# Round 229 six-crossing model review

No blocking defect was found for the pinned width-46 input. The six-crossing worker removes the native four-crossing boundary restriction and its closure-file dependency, translates the crossing budget correctly, and retains necessary path constraints and a complete witness audit. This is a source and saved-data review; no worker, solver, compiler or software test was run, and no search outcome was assessed.

## Source comparison and input scope

Read all of `prepare_six_crossings.py` (24 lines), `joint_six.py` (84), `run_six.py` (58), `joint_boundary.py` (91), and `prepare_width.py` (44). Read the six-crossing plan and compared the complete worker and runner diffs. Inspected the saved input status lists and independently recomputed every fixed-crossing budget from the seed and its two intervals.

The worker diff removes the loading and verification of `coverage45.json`, removes all boundary-selector variables and their omission constraints, retains an explicit width-46 guard, adds two to each replacement budget, and changes the final crossing audit from four to six. The runner changes its worker filename and removes the closure file from its input pins. No boundary condition remains in either active source.

The source graph contains 315 maximal contexts, with first interval starts 0–6 and second starts 98–142. Their closed intervals have a minimum index gap of 46, so vertices in different replacements are nonconsecutive in the assembled path. The plan lists exactly the 209 PENDING IDs and the other 106 STATIC_EXCLUDED IDs. All plan and preparation pins match. No input row has `INHERITED_EXCLUDED` status.

The inherited-status branch remains in the worker source, but it is unreachable for this pinned input and supplies no exclusion here. It must not be used to import four-crossing exclusions into a future six-crossing input. Likewise, the source file's descriptive four-crossing metadata records its original budget convention; the worker applies the explicit translation below and imposes no condition from that description.

## Crossing budgets and independent static geometry

The 192-vertex seed starts at 0, ends at 88 and has four coordinate-8 crossings. The appended edge from 88 to 24 has XOR 64 and contributes no coordinate-8 crossing. For each context, let \(f\) count the unchanged coordinate-8 edges outside the two replaced edge intervals. The saved budget is \(4-f\); adding two gives exactly \(6-f\). Recomputing all 315 rows found no discrepancy. The translated budgets are three in 21 contexts, four in 150, and five in 144.

Preparation excludes retained vertices and their forbidden neighbours, imposes the endpoint-24 restrictions, protects the two own anchors, deletes nonanchor vertices of degree below two, and restricts to the anchor component. Rejection uses only connectivity, size and bipartite colour capacity. None of these operations reads the crossing budget, closure data or boundary-omission conditions. The 106 initial static exclusions therefore retain their necessary interpretation for six crossings. This review did not rerun the complete domain preparation.

## Necessity of retained constraints

Each replacement selects exactly 47 vertices. Its prescribed anchors have selected degree one and every other selected vertex degree two, with degree counted in the induced allowed graph. These are necessary for an induced 46-edge path. The colour count is 24 vertices of the starting anchor's parity and 23 of the opposite parity. Original-source hints are suggestions to the solver and impose no additional restriction.

Each vertical-edge variable is exactly the conjunction of its two endpoint selections. Its sum therefore counts all selected coordinate-8 edges. The per-part equation is endpoint-face disagreement plus twice a nonnegative integer. Its upper bound uses the translated total replacement budget and contains every possible per-part crossing count. When both anchors have the same face and that face contains fewer than 47 allowed vertices, zero crossings cannot support the path, so the retained minimum of two is necessary. The sum over both parts is precisely \(6-f\); no individual crossing allocation is fixed beyond these conditions.

Every equality or cube adjacency between selected vertices in the two separated blocks is forbidden. This includes their anchors and is necessary because all such pairs are nonconsecutive in the complete path. There is no mutual-contact requirement or short-move closure condition.

The degree relaxation can contain the endpoint path together with disconnected cycles. The route extraction follows the unique selected continuation from one endpoint to the other; the two odd-degree vertices belong to the same component. Every other selected component has degree two throughout. A cycle cut requires omission of at least one vertex from that cycle, which every induced path must satisfy. This argument is independent of whether the total crossing target is four or six.

## Witness and result interpretation

After cycles are absent, reconstruction retains the original outside positions, uses both anchor-to-anchor routes, and appends 24. The final audit requires 193 distinct vertices, adjacency exactly for consecutive indices across every pair, and exactly six coordinate-8 crossings. The fixed anchors and source slices preserve endpoints 0 and 24. Thus a recorded witness must be an actual induced 192-edge snake in the specified construction family.

`COMPLETE_COVERAGE` records that all requested IDs received result rows; it may coexist with UNKNOWN or other inconclusive statuses. Only terminal INFEASIBLE rows support individual native exclusions, and unresolved or interrupted rows must remain unresolved. The plan itself is PREPARED_UNEXECUTED and establishes no outcome. Solver contradictions and complete traversal have no Lean certificates here.

The scope is this fixed seed, appended endpoint 24, retained anchors and outside indices, two length-preserving width-46 replacements, and exactly six coordinate-8 crossings. Other crossing counts remain separate families. No result about a new witness or a global bound follows from this source review.

## Pinned evidence

| File | SHA256 |
|---|---|
| `scripts/prepare_six_crossings.py` | `43f25862b38ddd3365e4d7231180c3763b5e075693b6fa8fc71f70aa71c8db0f` |
| `scripts/joint_six.py` | `0ceddd6885865c6e2a3f1ff446ece4443ef8f5333afc4cdd0e3f92f86c3f9f5c` |
| `scripts/run_six.py` | `aa882162abb1fc3f14915f002b67b93fa3fd6704f86adbc10cefedc06577def3` |
| `scripts/joint_boundary.py` | `5b92bc0b02f60650f6bd1c482fd88868ed106101780c52392f1304088fe2b85b` |
| `scripts/prepare_width.py` | `391211994dabe1770ea0db0cd0be97f461f4262736a70f294a31c35d49bdc4be` |
| `data/six-crossing-plan.json` | `ab1e57e766811c3b1f40f9f21394ef5ac6c08422af22764ccee3bef70541c230` |
| `data/regions46.json` | `94ea1833e98f07b3f4327b2f06056847474c75dbcda1f30cb2abe7bb4bd9cca6` |
