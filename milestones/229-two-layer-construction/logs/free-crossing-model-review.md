# Round 229 unrestricted-crossing model review

No blocking defect was found for the pinned width-46 input. The worker removes the exact total crossing count and every use of the saved crossing budget. The retained parity bound contains every possible crossing count allowed by the actual vertical-edge set. This extends the reviewed construction family to any feasible total crossing count without a prior-width boundary premise.

Read all of `prepare_free_crossings.py` (22 lines), `joint_free.py` (82), `run_free.py` (58) and `free-crossing-plan.json` (331). Compared the complete worker and runner diffs against the reviewed six-crossing sources, and compared the plan's IDs and pins against the unchanged preparation. No worker, solver, compiler or software test was run; no mutable run output or search outcome was assessed.

## Removed restrictions

The worker no longer increments `replacement_crossings`, imposes no sum of vertical edges equal to that field, and does not assert a final total of six. There are zero remaining references to `replacement_crossings` in `joint_free.py`. Its parity variable uses `len(edges)//2`. The earlier boundary selectors and closure-file dependencies remain absent, and the runner introduces no additional mathematical condition.

The arrays collecting all vertical edges and their counts remain as unused bookkeeping; they do not create a total-count constraint. The original seed hints likewise impose no required selections. Neither the four-crossing description stored in the original preparation nor any outcome of the six-crossing search is consulted as an exclusion premise.

The prepared graph is unchanged, with SHA256 `94ea1833e98f07b3f4327b2f06056847474c75dbcda1f30cb2abe7bb4bd9cca6`. The free plan contains exactly its 209 PENDING IDs and 106 STATIC_EXCLUDED IDs. The total-crossing field is null, all plan pins match, and there are no inherited-exclusion rows. The dormant `INHERITED_EXCLUDED` branch is therefore unreachable. Future input must not populate it with exclusions proved only under a prescribed crossing count.

## Necessity of retained constraints

Let \(M\) be the number of available vertical edges in one part, \(c\) the number selected, and \(p\in\{0,1\}\) its anchor-face disagreement. Every actual path has \(0\le c\le M\) and \(c\equiv p\pmod2\). Thus \(h=(c-p)/2\) is a nonnegative integer with \(h\le\lfloor M/2\rfloor\). The retained equation \(c=p+2h\) with this bound excludes no actual crossing count. An allowed auxiliary value could formally exceed the available-edge sum in one parity case, but the equation itself prevents that value from being selected; it creates no additional restriction on valid paths.

Same-face anchors with fewer than 47 allowed vertices in that face still require at least two crossings. This is a necessary capacity condition independent of a prescribed total. The other retained requirements are unchanged: 47 selected vertices per part, 24 of the starting parity and 23 of the other, degree one at the two selected anchors, degree two at every other selected vertex, and mutual equality/adjacency exclusions between the two separated blocks.

The initial domains and static exclusions use retained-vertex avoidance, endpoint-24 avoidance, anchor-protected degree peeling, connectivity, size and colour capacity. These operations were reviewed as crossing-independent in `six-crossing-model-review.md`. They remain valid for arbitrary crossing totals. This extension did not rerun or independently reconstruct all domains.

The degree relaxation permits an endpoint path plus disconnected cycles. The unchanged extraction and cycle-cut procedure requires omission of a vertex from each discovered cycle. Such a cut is necessary for every induced path, regardless of its crossing count. No four-crossing or six-crossing argument is used by these cuts.

## Witness audit and interpretation

The final reconstruction retains the prescribed outside positions and anchors, inserts both routes and appends 24. Its audit still requires exactly 193 distinct vertices and checks every pair for adjacency exactly when consecutive. After these checks, the worker counts coordinate-8 edges in the complete reconstructed path and records the value as `total_bit8_crossings`. It does not reject a candidate because that value differs from four or six. The source slices and fixed anchors preserve endpoints 0 and 24, so a recorded witness is an actual induced 192-edge path in this retained-index family.

Every actual candidate from the corresponding exact-four or exact-six family satisfies this broader model. More generally, all crossing totals compatible with the fixed geometry are permitted. Endpoint parity and retained outside edges still constrain what is geometrically possible; those are consequences of the construction rather than an imposed total.

The scope remains the fixed seed, appended endpoint 24, two length-preserving width-46 blocks and unchanged anchors/outside indices. It is not a search over arbitrary Q9 snakes. The plan is PREPARED_UNEXECUTED. A future `COMPLETE_COVERAGE` label means all requested IDs received records and must still be distinguished from terminal infeasibility of every row. Unknown, timed-out or interrupted rows establish no exclusion. This review supplies no witness, native outcome, Lean contradiction certificate or global bound.

## Pinned sources

| File | SHA256 |
|---|---|
| `scripts/prepare_free_crossings.py` | `edd5abee3149dc5ffbe6e1ecf18ebb74600dbda9367a28377e3bbda925b91fa6` |
| `scripts/joint_free.py` | `352ccb07b4701ba3c86b837dc8c1e8182557f0e40ba6549bc3aa37949a52d888` |
| `scripts/run_free.py` | `4204fa91eb5978ca5c9ce4bdb5802cc21d3cd06c91530379c530be21af81a295` |
| `data/free-crossing-plan.json` | `f6a4e512b339687f87d431652cb383d78d0292be824bcd851fb52ea76c09b7f4` |
| Reviewed `scripts/joint_six.py` | `0ceddd6885865c6e2a3f1ff446ece4443ef8f5333afc4cdd0e3f92f86c3f9f5c` |
