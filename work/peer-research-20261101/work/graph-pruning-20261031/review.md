# Independent graph-pruning review — 2026-10-31

Both proposed rules are safe as stated with the conventions below. They are search-node upper bounds for a fixed prefix, not new global bounds for Q9. No solver file was changed.

## 1. Residual graph and units

Let P=(p0,...,pt=h) be an induced path. Write O={p0,...,p(t-1)}. Use the graph induced on {h} union (V minus N[O]), then restrict to its h-connected component H. Every valid future vertex must lie here: it is new and cannot be adjacent to any old vertex in O. The explicit exception retaining h is essential, because h is adjacent to its predecessor. The graph may retain vertices that cannot coexist in a future induced path; that is safe for an upper-bound relaxation.

All bounds below count vertices of a continuation including h. Thus if B is the computed bound, at most B-1 new vertices/edges can be added. If the prefix has t edges, its final edge count is at most t+B-1. A singleton H={h} has bound 1 and must not be treated as an empty block tree.

## 2. Block-chain containment

Include bridge edges as two-vertex blocks. The block-cut tree of the connected graph H has a block node for each block and an articulation node for each articulation vertex, with the usual incidence edges. If h is an articulation, root at its articulation node. Otherwise root at its unique block node. The singleton case is handled separately.

For every rooted leaf-block chain L, let U_L be the SET UNION of the full vertex sets of every block on L, plus h. In particular, include articulation vertices belonging to such a block even when their articulation nodes are not on L. Count shared articulation vertices once.

Claim: every simple path beginning at h has its vertex set contained in some U_L.

Proof. For a path with at least one edge, assign each path edge to its unique block. Suppress consecutive repetitions of a block. A change of block can occur only at their shared articulation vertex. The resulting sequence follows the unique corresponding route in the block-cut tree. It cannot return through an articulation vertex already crossed: the original path is simple. Nor can it enter a branch of the tree and return to its attachment, since the attachment is one specific vertex and returning repeats it. Hence its used-edge blocks form a single chain away from the prescribed root. Every path vertex is incident to a used edge, hence belongs to one of those full blocks. The finite chain can be extended away from the root to a leaf block; enlarging the union preserves containment. A zero-edge path {h} is contained in any rooted leaf chain. This proves the claim.

Note the used-edge formulation: merely touching a vertex that belongs to several blocks does not mean that the path traverses all those blocks. Treating all incident block memberships as visited tree nodes would be incorrect.

## 3. Bipartite endpoint-aware bound

For each U_L in a bipartite graph, let s be its number of vertices of the same color as h, and o its opposite-color count. A path beginning at h alternates colors. If its length in vertices is even, it uses equally many of each color and is at most 2s and 2o. If it is odd, it uses one more same-color vertex, and is at most 2s-1 and 2o+1. In both cases its vertex count is at most min(2s,2o+1). Therefore

    B_block = max_L min(2*s_L, 2*o_L+1)

is a safe bound on the continuation's vertex count. Hypercube colors are popcount parity. This expression is monotone when the set U_L is enlarged, justifying extension of a partial chain to a leaf. Evaluate the colors of actual vertex IDs, not Tarjan discovery indices.

### Concrete Q4 counterexample to omitting off-chain articulation vertices

Take V={0,1,3,7,6,4,11,14}, with all cube edges among these vertices. The six core vertices form the induced cycle [0,1,3,7,6,4]. The leaf 11 is attached to 3; leaf 14 to 6. Root h=0. The induced path [0,1,3,7,6,14] has six vertices.

The leaf-block chain ending at {6,14} must still count core articulation 3, although its articulation node is off that chain. Conversely the chain ending at {3,11} must count core articulation 6. Omitting the off-chain articulation gives same-color count 2 and opposite count 4 on each chain, falsely bounding every continuation by 4. The correct complete block union gives the safe bound 6. Assigning weight only to globally non-articulation vertices is even less safe. The reproducible test checks the cube's full pairwise inducedness of the six-vertex witness.

## 4. Arbitrary vertex-separator bound, including two-vertex cuts

Let K be any k-vertex set in H; it need not be a minimal separator. Delete the vertices of K from a simple path R beginning at h. If R uses r vertices of K, what remains consists of at most r+1 contiguous nonempty path segments. Each segment lies in a connected component of H-K. Thus R visits at most r+1 <= k+1 DISTINCT components. Several segments can lie in the same component, which only decreases the number of distinct components.

If h is not in K, its component C_h must be visited. Therefore, writing the sizes of all other components in descending order d1>=d2>=...,

    |R| <= k + |C_h| + sum of the largest at most k other component sizes.

If h is in K, the general safe bound is

    |R| <= k + sum of the largest at most k+1 component sizes.

It can be sharpened to the largest at most k components: the first vertex is already a deleted K vertex, so removing K leaves at most r nonempty segments. For k=2 the requested weaker bound is safe in both cases; the h-not-in-K form uses C_h plus the two largest other components.

Proof of the capacity step: every used K vertex is counted within k, and the path uses at most the full vertex set of each visited component. Components partition H-K, so there is no overlap. Disconnected components of the original residual graph can first be removed by restricting to H, improving the bound.

### Risks when strengthening component capacities

The safe component capacity above is its vertex count, or another bound on the TOTAL number of its vertices occurring across all visited segments. A longest-single-path bound for that component is not automatically such a capacity: the global path may leave and re-enter a component via distinct K vertices.

For example, let one component be the tree obtained by subdividing every edge of a four-leaf star once. Label its center c, intermediates u1..u4, leaves v1..v4. Its longest simple path has 5 vertices. Add K={a,b}, edges v2-a-v3-b-v4. Then [v1,u1,c,u2,v2,a,v3,b,v4] is an induced path of 9 vertices. Deleting K leaves the original nine-vertex star component. Replacing its cardinality by its single-path maximum 5 would yield the FALSE bound 2+5=7. The cardinality rule yields 2+9=11 and is safe. Thus do not combine separator decomposition with single-component path bounds without tracking multiple allowed segments/ports.

The separate B_block and B_separator bounds can always be combined by taking their minimum. Applying another independently sound cardinality/separator bound inside each induced H[U_L], with the same start h, is also safe, then maximize over chains. Do not sum unrelated per-chain capacities or require an induced path to use all vertices of a chain union.

## 5. Independent exhaustive controls

`independent_checks.py` implements an independent Tarjan edge-stack decomposition, rooted full-block unions, simple-path enumeration, and separator size bounds. It exhaustively checks every simple undirected graph on five labelled vertices:

- 1,024 graphs and 5,120 root cases;
- 53,760 rooted simple paths: every path is contained in a rooted leaf-chain full union;
- 2,015 bipartite-root cases satisfy the parity bound;
- 81,920 separator/root cases for |K|=0,1,2 satisfy the cardinality bound;
- the explicit Q4 omission counterexample gives true path size 6, correct bound 6, incorrect bound 4.

All checks PASS. Finite exhaustive checks support implementation choices; the proofs above establish the general rules. No performance benefit has yet been measured for the user's solver.

## 6. Prior literature and novelty scope

These are established admissible longest-path search ideas, not a claim of a new theorem. Dahan, Tabib, Shimony and Felner, *Generalized Longest Path Problems* (SoCS 2022), section 2.2, explicitly describes retaining blocks on the start-to-target block-cut route, attributing the hBCC heuristic to Cohen, Stern and Felner (2020), and discusses application to snake-in-the-box. Its sections 5.1 and the background also discuss separator-pair/SPQR reasoning. The free-endpoint version here takes the maximum over possible leaf directions; the parity and elementary separator cardinality arguments are proved independently above. This review does not establish priority for the exact combined implementation or claim literature novelty.

Primary source: https://ojs.aaai.org/index.php/SOCS/article/download/21752/21516/25795 (9-page paper, read online 2026-10-31).

## 7. Review of the actual `graph_solver.py` implementation

Source reviewed: SHA256 `64dad599c7b9c4b97718720c92c81c59445fba77b90ef0a805d2d7c9eceb18bb`. `validate.py` was also read. No solver source was modified. Independent controls are in `review_implementation.py` and `implementation_independent_review.json`.

### Cycle-block penalty: PASS

The implementation detects a cycle block only when its vertex set has at least four vertices and every vertex has degree two within that block. A connected block satisfying this predicate is an induced cycle. For the actual chain of blocks containing edges of an induced continuation, at least one vertex of each such cycle block is absent: selecting all vertices would preserve every cycle edge in the induced subgraph and could not be an induced path. Moreover a vertex shared by two consecutive actually used blocks is their transition articulation and is selected. Therefore each omitted vertex can be charged to at most one cycle block on that actual chain; the path has at most |union|-number_of_cycle_blocks vertices.

For an upper bound one then extends the actual used-block chain to some leaf. This extension does not require each added cycle block to have a distinct genuinely omitted vertex. Instead, the numerical expression is monotone: a new block B shares exactly its attachment vertex with the previous union, so |union| increases by |B|-1, while the penalty increases by at most one. The net gain is at least |B|-2 for a cycle (at least 2) and |B|-1 for another block (at least 1). Traversing an articulation node alone does not change either quantity. The parity capacity of the union is independently monotone. Thus their minimum is also monotone, exactly matching the code's leaf-only evaluation. This argument avoids an invalid direct omission count on wholly unvisited added blocks.

### Simultaneous leaf peeling: PASS

For any current simple path beginning at the retained root h, a vertex of current graph degree at most one other than h can occur only as its final vertex. Consequently each simultaneous peel round removes at most one vertex from the current path, and its remaining prefix is still a valid rooted path in the surviving graph. After r rounds, original path length <= surviving vertex count+r. The implementation removes all non-root degree-zero/one vertices together, counts one per round, and terminates on the unpeeled core. Including degree-zero vertices is safe; they cannot occur on a nontrivial rooted path. The guarantee applies even to simple paths, so also to induced paths.

### Search residual graph and memo: PASS within the fixed instance

Initialization sets `banned` to the closed neighborhoods of all prefix vertices except its head. Every transition moving h to v adds the closed neighborhood of h. Thus at every recursive state,

    banned = N[used vertices except current head].

The candidate formula removes used/banned vertices, then restores h, and the flood fill retains only its connected component. Candidate edges from h preserve adjacency to h while excluding adjacency to every older selected vertex. The requested residual vertex budget `target-len(path)+1` correctly includes h once.

The memo key `(h, used)` determines banned, residual graph, and used-set cardinality, hence the remaining target in this fixed instance. The chronological order of the old induced prefix is irrelevant to future choices. Memoizing a state only after a sound bound rejects it or after every child returns False is safe. A child returning None for budget exhaustion propagates immediately without adding that ancestor to `failed`. The SAT branch independently validates the witness. Memo entries must remain local to this fixed domain, graph and target; importing them into another instance would require those instance parameters in the cache identity.

The Tarjan implementation uses the full block vertex sets and bitwise set union, so the earlier off-chain-articulation counterexample is handled correctly. Bridge and isolated-head cases are represented. Separator bounds count full component vertex sets, avoiding the unsafe component single-path substitution described above.

### Independent controls

The new reviewer uses its own direct induced-path recursion (without Tarjan, residual pruning, or memo) as the exact oracle. It checked:

- all 1,024 five-vertex graphs and all 5,120 roots: raw cycle-penalty block bound and leaf bound never underestimate the oracle; 420 cases exercise a cycle penalty;
- 1,274 cube domain/prefix cases: every nonempty Q3 induced-domain/root pair and 250 deterministic random Q4 domains with generated induced prefixes;
- 25,480 complete searches: all five pruning modes, memo both on/off, and targets at the oracle maximum and one edge above it. Every SAT/UNSAT status agrees; every returned witness is independently checked pairwise and against domain/prefix constraints.

All PASS. These finite controls supplement the general arguments; they do not certify exhaustive Q9 exclusion. The existing n9 target235 node-limited UNKNOWN result remains UNKNOWN, and a nonzero block-prune count is evidence of use rather than evidence of a global bound or measured net speedup.

Input-hardening limitation: the class assumes a nonnegative finite cube-domain bitmask and sensible n/budgets. A negative domain can make the bit iterator nonterminating; native recursion can overflow on larger dimensions. These are interface robustness concerns for unsupported inputs, not counterexamples for the reviewed Q9/full-domain invocation. Validate explicit custom domains before exposing this API more broadly.
