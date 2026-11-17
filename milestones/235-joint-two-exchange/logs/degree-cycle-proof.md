# Exact selected degrees with cycle exclusions

The proposed model and the saved degree_search.py source were reviewed without running a solver, compiler, or tests. No new Lean module is needed for the cycle-cut principle: the accepted Cycle218.cycle_not_contained and Cycle218.cycle_cut already apply. The finite extraction of each literal cycle remains a separate obligation.

## Model and non-selected vertices

Let $x_v$ indicate selection of cube vertex $v$, and let $e_v$ be an endpoint flag on the designated majority parity class. Set $e_v=0$ on the minority class. Require exactly 96 selected minority vertices, 97 selected majority vertices, two endpoint flags in total, and $e_v\leq x_v$.

For every selected vertex require

\[
\sum_{w\sim v}x_w=2-e_v.
\]

The sum counts all selected cube neighbours. There is no edge-choice variable allowing an ambient edge to be ignored. Thus it is the degree in the induced selected graph.

This equality must be conditional on $x_v=1$. An unselected vertex may have any number of selected neighbours, from zero to nine. Requiring zero selected neighbours, or imposing an unconditional degree-two upper bound on it, would remove valid snakes. The inspected source correctly uses conditional enforcement, and $e_v\leq x_v$ makes every unselected endpoint flag zero.

If a linear inequality encoding is used instead, the accepted signed degree lemma specializes in $Q_9$ to

\[
2x_v-e_v\leq S_v\leq9-7x_v-e_v,
\qquad S_v=\sum_{w\sim v}x_w.
\]

With Boolean selections and endpoint flags, $e_v\leq x_v$, and $0\leq S_v\leq9$, this imposes exactly the required equality when selected and no additional restriction when unselected. The actual implementation uses the simpler conditional equality.

For a saved 96-vertex minority class $U_0$, exactly two replacements are expressed by

\[
\sum_{v\in U_0}x_v=94.
\]

Together with the total minority count of 96, this means exactly two omissions and two outside insertions. It describes exactly two replacements, not an unrestricted number or an at-most-two family. Every 192-edge snake with the prescribed complete minority class and exchange count satisfies the model, with its actual two majority endpoints flagged.

## Structure of a feasible selection

The selected induced graph is finite, simple, and undirected. Exactly two selected vertices have degree one, and every other selected vertex has degree two. No selected vertex is isolated.

A finite connected graph with maximum degree two is a path or a cycle, except for a singleton; the singleton case is excluded here by the positive degrees. Every path component has two degree-one vertices and every cycle component has none. Since there are exactly two degree-one vertices overall, there is exactly one path component, containing both endpoint flags, together with zero or more disjoint cycle components.

The selected degree sum is $2\cdot193-2=384$, so the graph has 192 edges even when disconnected. This edge total alone is not a witness: cycles may account for part of it. Each cycle has even length, at least four, because the cube is bipartite.

If no cycle component remains, all 193 selected vertices lie on the unique path. Traversing it from an endpoint yields 192 edges and no repeated vertex. Its inducedness follows because the adjacency used in traversal is the complete cube adjacency restricted to the selected set. The independent all-pairs check remains a useful final witness validation and is present in the inspected source.

## Why each cycle cut remains valid

Let $C$ be the distinct vertices of an extracted cycle, with their consecutive and closing cube edges verified. Every actual induced path obeys

\[
\sum_{v\in C}x_v\leq |C|-1.
\]

If a future selection retained all of $C$, every edge of that ambient cycle would still be present in its induced selected graph. Changing vertices outside $C$ cannot remove those edges. Adding a connection to the cycle would raise a cycle vertex's selected degree above two; leaving it unconnected would retain a cycle component. More generally, an induced path contains no cycle as a subgraph, whether or not that cycle was an entire component when first discovered.

This is the scope of the accepted Cycle218 theorem: a distinct ambient cycle cannot have all its vertices in an actual indexed induced path. It does not require the cycle to be chordless or to remain a component in the later selection. The cut is therefore independent of the old endpoint flags, other selected vertices, the saved base class, and the exchange choice. It can be reused in the same cube whenever its literal cycle has been verified.

The inducedness requirement is essential. A merely simple path could visit every vertex of an ambient cycle while omitting a closing edge. That possibility is absent here because selected edges are determined by selected vertices and cube adjacency.

The inspected source extracts connected components from the full selected graph. A component not containing either endpoint has degree two at every vertex and is consequently a cycle. Its sorted vertex set suffices to state the occupancy cut. An independent audit can reconstruct a cyclic ordering from that set and cube adjacency to instantiate the general cycle theorem. The present review does not supply that literal Lean assembly.

## Completeness and stopping semantics

Every added cycle cut preserves every genuine target snake, and each excludes the current disconnected selection because that selection contains all vertices of the extracted cycle. The source adds a cut for every cycle component found. A previously cut complete cycle set cannot reappear in a later feasible selection; a repeated-cut assertion failure would indicate an implementation or evidence problem, not an exclusion result.

With finite Boolean selections, persistent valid cuts, and conclusive solution of every successive query, the process must eventually find a connected target or prove infeasibility: each disconnected iteration excludes its current selected set, and only finitely many selected sets exist. This is a logical termination statement without a useful practical time guarantee.

The outcomes must retain their actual scopes:

- A connected feasible selection with the complete path check passed is a 192-edge witness in the stated family.
- A disconnected FEASIBLE or OPTIMAL degree assignment is not a snake witness; it supplies valid cycle cuts.
- INFEASIBLE for the accumulated model excludes the prescribed exchange family, provided the initial model preserves that family and every imported cut is valid.
- UNKNOWN, a query time limit, a per-base time limit, global budget exhaustion, or a resource interruption leaves that base unresolved.
- COMPLETE_QUERY_BATCH in the inspected script means all requested base entries were visited. It does not imply that every row is INFEASIBLE; individual UNKNOWN or TIME_LIMIT rows remain unresolved.

The source records the selected vertices, endpoints, component sizes, and the originating iteration for each cut, and exports each queried model with its hash. These are suitable inputs for a separate replay of literal cycle validity and model evolution. Native infeasibility still depends on the solver unless its contradiction is separately certified.

The configured requested base list covers only those listed bases. A conclusion for all saved classes requires complete coverage of that larger inventory. No such completeness or numerical result is asserted by this review.

## Evidence inspected

The degree-search source inspected here has SHA-256 ea4685761c79ae140d07023477c0bd9cbc67ac5301a6c4176079a5f923e59e60. Its conditional degree enforcement, endpoint restriction, parity totals, and exact exchange equation agree with the model above.

Cycle218 has a PASS receipt with hash d90cc4c8d8a9efbbceaa8ca37de70059d6a3bbbfbe2029ae3d436db704ccb996 and source hash 013c4a3afcf4d965d17e274a264775ceb197327c4d05ee70f77a67aa3de000d6. Degree219 has a PASS receipt with hash 13ee4f92af48fcc59cfb04ec28b168ea5f73ac0e623b3979137b69cab4c7e0c1 and source hash a3fc1ff1d763184c1331d0b9841edad92873738d46a0b0753727c4e709400a6e. For both modules, the current source, object, and compiler-log hashes matched their receipts.

No blocking mathematical defect was found in the stated model and cycle-separation method. This is a source and mathematical review; it reports no native search outcome or global upper bound.

## Exact accepted cycle-cut dependency

- Source: E:/Snake-in-a-box/milestones/218-direct-partner/lean/Cycle218.lean.
- Receipt: E:/Snake-in-a-box/milestones/218-direct-partner/data/Cycle218-audit.json.
- Object: E:/Snake-in-a-box/milestones/218-direct-partner/build/Cycle218.olean, SHA-256 f29cf9400b91481d9668edad1462ee2b4ce515fe53b34f8d9bb4e99a55fae3e9.
- Compiler log: E:/Snake-in-a-box/milestones/218-direct-partner/logs/Cycle218-1794681204789359000/compiler.log, SHA-256 d6004c5537b4906b1f082ef81fb476590aa96f828be4c58d3e3fb2866c177024.

The directly reusable theorem is Cycle218.cycle_cut. It takes an actual LayerJoining.InducedPath, an injective cyclic ordering of $n+3$ ambient vertices, symmetry of adjacency, all successive cycle edges and the closing edge, and a Boolean selection whose selected cycle vertices occur in the path. Its conclusion is that at most $n+2$ cycle vertices are selected. Cycle218.cycle_not_contained is the preceding containment theorem used in that proof. Both reports list only propext, Classical.choice, and Quot.sound.

For a new literal cut, the remaining bridge is to verify the extracted cyclic ordering, its distinct vertices, and its cube edges, and to interpret the model selection as the vertices of any hypothetical target path. The theorem imposes no chordlessness condition and no assumption that the cycle remains a component after a later selection change. No additional generic Lean proof is required for these occupancy cuts.
