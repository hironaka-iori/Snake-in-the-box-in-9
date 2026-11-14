# Round 218 direct-partner model source review

Result: no blocking source-level defect found. Read the complete partner_search.py and run_partner.py, the generic Cycle218 statement/proof source, saved graph metadata, and relevant installed OR-Tools API declarations. No solver, compiler, software tests, or new query was run by this reviewer. Runtime results and exported model files require a separate audit after termination.

## Exact search scope and necessary constraints

The model seeks an arbitrary induced path of 93 edges in Q8, starting at either endpoint 0 or 78 of the fixed saved 98-edge parent. It permits every cube vertex except the parent's other 98 vertices. There are no interval-replacement constraints, fixed coordinate schedules, old nogoods, symmetry restrictions, or fixed second endpoint in the source.

For each root, V is reconstructed directly from all 256 vertices and the parent vertex set. The saved allowed-vertex list must equal this reconstructed list exactly. The parent is checked for 99 distinct in-range vertices and for the induced-path condition over every pair. Both roots have even parity. A 93-edge path rooted at an even vertex necessarily has 94 vertices, 47 of each parity, and an odd second endpoint. The model therefore preserves every intended partner through its 47/47 cardinalities and free choice among all 79 allowed odd vertices.

The root is selected and has selected-neighbour degree one. Exactly one odd endpoint variable is true, and endpoint <= selection prevents an unused endpoint. Every other selected vertex has degree two. Degree equations for nonroot vertices are conditional on selection, so unselected vertices are unrestricted. Adjacency is the full induced Q8 adjacency on V, rather than a restricted transition table. These equations are necessary for every intended path, while allowing disconnected cycles as a relaxation.

The two degree-one vertices must lie in the same component: a finite undirected component cannot have exactly one odd-degree vertex. A connected finite component with the stated degrees is a path; each other component is a cycle. Thus the assertions used during component extraction do not impose an additional restriction on a valid solution of the degree equations.

## Static and iterative cycle cuts

Each static cut is checked to contain distinct allowed vertices, at least three in number, and induced degree two at every vertex. Such a nonempty finite simple subgraph contains a cycle; consequently an induced path cannot contain the entire set. Connectedness of a static cut is unnecessary for this implication. The saved counts are 279 cuts at root 0 and 274 at root 78, from squares and the listed six-cycles. Their absence from a larger cycle catalogue does not affect soundness or path coverage.

Dynamic cuts are obtained from nonroot connected components of an actual relaxation selection. Every listed vertex has induced degree two within that component. The inequality omitting at least one vertex is therefore necessary for every induced path. All such cuts remain in the model on subsequent solves. Every disconnected selection yields at least one new cut; previously forbidden components cannot recur in a satisfying assignment. A duplicate assertion failure would be an execution error, not an exclusion.

The algorithm may stop before all relevant cycles are encountered. Within its time budget it preserves every valid path at each iteration. If a remaining-budget iteration returns UNKNOWN, or the budget expires after adding cuts, the result stays UNKNOWN. This is bounded search, with no guarantee of finding an existing path in the allocated time.

## Status and construction validation

FEASIBLE and OPTIMAL solver responses first undergo explicit cardinality, endpoint, degree and component checks. They are reported as FEASIBLE only after extracting one connected 94-vertex path and checking every pair for the induced-path condition. A disconnected relaxation selection is saved as such and never reported as a snake.

For a valid partner q, the parent is oriented to end at the selected root. The output joins that parent to q lifted by 256, giving 193 distinct Q9 vertices and 192 edges. The source checks that the projected vertex sets intersect exactly at the root and then directly checks the induced-path condition over every pair of the joined sequence. This validates the proposed construction independently of the solver's encoded degree equations.

INFEASIBLE is preserved as the native solver status. Because every added cut is necessary, it would apply to this exact fixed-parent, fixed-root query; it is neither a global bound nor a separately replayed proof certificate. MODEL_INVALID is also preserved by its exact name and must be treated as a model/execution problem. UNKNOWN and resource interruption give no exclusion. The wrapper's ACCEPTED_NATIVE_RESULT denotes a successful recorded invocation, not mathematical certification of every possible status.

## Resource wrapper and API

The wrapper runs the requested roots sequentially. It rejects existing root directories, checks the fullgraph lock, acquires its own lock, and waits for a startup gate before creating a root directory. The child is limited to one solver worker and receives the remaining time budget at each iteration. The wrapper independently checks memory, free memory, other Lean processes, resource-query failures and a wall-time allowance. On any guard condition it terminates the child and records INTERRUPTED. A valid-looking partial result is not accepted after such a stop. Nonzero exits are likewise interrupted; stderr and stdout hashes are retained. The wrapper proceeds to the next root only after an accepted invocation, and stops after a validated FEASIBLE result.

Input/script pins are rechecked after each child ends. The output source/seed/graph/model hashes and execution receipt permit the later independent record audit. Atomic result/checkpoint writes avoid accepting a partially written JSON file. Import/model-construction/export failures produce failed executions rather than native exclusions.

Installed OR-Tools identifies itself as 9.15.6755. Source inspection confirms the status_name argument form and the wall_time, num_branches and num_conflicts property access used here. No API invocation or model validation was executed by this review.

## Remaining boundaries

This review establishes that the written constraints are necessary for all 93-edge partners in the stated fixed-parent model. It does not verify the eventual exported protobuf against the source, every saved cycle row, actual solver iterations, executable/library integrity, or a terminal result. The general cycle theorem supports the mathematical cut; the complete Python/CP-SAT encoding and execution are outside that checked theorem. No improvement to the known lower bound is claimed without an independently inspected output path.

## SHA-256 snapshot

- `scripts/partner_search.py`: `e1dd8547190b5111e003d81e4e70fbeddcc292447eb29684adf103c82a787100`
- `scripts/run_partner.py`: `b83a2c9662a607d693ace6e47d210753cc38b06c2968ffd3d83d2b93157d3c63`
- `scripts/native_resources.py`: `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413`
- `data/seed98.json`: `2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5`
- `data/complement-graph.json`: `6af4976a40d897be2c43790c75b66fac0473f0a97226d3fdb106140744a94c82`

## Retry-source addendum: restricted library threads

The complete original review above is retained byte-for-byte as a prefix, with SHA-256 `053941293564dc8434b585c2b89b244b4b048bb391e0da65c5e7ee3779065a7d`.

Independently read the complete diff against the archived original sources in data/root-0. partner_search.py only adds an explicit output directory and checks its resolved containment within this milestone's data directory. run_partner.py writes to fresh data/threads1/root-* directories, passes that path to the child, records four thread-environment settings, and supplies them through the actual subprocess environment. The four settings are OPENBLAS_NUM_THREADS, OMP_NUM_THREADS, MKL_NUM_THREADS and NUMEXPR_NUM_THREADS, each set to 1. The batch-progress file also moves into threads1.

The mathematical model, seed/graph input, solver parameters, degree and cycle constraints, iteration handling and final path validation are unchanged. Original output directories remain untouched. There is no blocking source defect in this retry diff. A lower memory use is a hypothesis to be assessed from the retry's actual resource record; the diff alone establishes no performance result.

The preserved first invocation records INTERRUPTED/MEMORY_LIMIT, exit 1, about 2.734 wall seconds and a sampled peak private memory of 590,295,040 bytes. Its stdout and stderr are empty; the directory contains no exported model or result. These inspected records establish no solver conclusion. Its original source snapshots have exactly the source hashes listed above; the changed current files must not be substituted when checking that historical receipt's pins.

Retry source SHA-256 values:

- `scripts/partner_search.py`: `cebcf267fe2ba1ae2d19bfb917246e296221b0e3f719500b7e2e42c7190b45c5`
- `scripts/run_partner.py`: `107140d550ed4ec8706d64f324fdda888f7e8bf834db396e2e428baa930aca97`
- Preserved `data/root-0/execution.json`: `1e228b4468670c0c7f75d936fe19fe3d97e31c030ffb740aa9b45015c3a293e8`

This addendum reviews the retry source and preserved initial failure only. The retry's mutable execution state was not inspected, and no solver or tests were run by the reviewer.
