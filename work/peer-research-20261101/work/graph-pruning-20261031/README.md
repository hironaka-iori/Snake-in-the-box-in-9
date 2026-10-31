# Q9 graph-theoretic pruning, 31 October 2026

This continues the repository's current research; it does not reset the global baseline to 254/255 from the older pasted directive. The inherited repository reports a contributor-checked upper bound of 235; this work does not independently rebuild that global theorem and proves no new global numerical bound. The global target tested here is the existence of a 235-edge path, whose exhaustive exclusion would imply 234. Both bounded global probes remain UNKNOWN.

## Main concrete result

A valid 84-vertex prefix encountered during that search has 165 residual vertices. A 235-edge completion needs a suffix of 153 vertices, including its head. Reachability permits 165, parity permits 164, leaf peeling permits 155, and the complete-block-chain bound permits 152. A separate certificate of 33 vertex-disjoint endpoint/claw groups forces 34 omissions and permits only 131 suffix vertices. Thus this particular prefix cannot extend beyond 213 edges. This is a restricted prefix exclusion, NOT a bound on all Q9 paths.

`check_branch.py` independently reconstructs the residual graph and splits blocks by repeated articulation removal, rather than the solver's Tarjan algorithm. `check_claw_certificate.py` independently checks all group adjacencies, vertex-disjointness and omission counts. Both checks pass.

## Rigorous bounds and their exact scope

Let P=(p0,...,pt=h) be an induced prefix in a graph G; let O be all its vertices except h. The residual graph is the component of h in G[{h} union (V(G) minus N[O])]. Every appended vertex belongs here because it is new and has no edge to O. Keeping h explicitly is necessary. Every bound B below counts suffix vertices INCLUDING h. The resulting full path has at most t+B-1 edges.

1. **Reachability and parity (PROVED, ordinary mathematics).** Restrict to that component. If it has s vertices of h's bipartition color and o of the other color, an alternating path from h has at most min(2s,2o+1) vertices: even paths use equal counts and odd paths use one more vertex of h's color.

2. **Leaf peeling (PROVED).** Retain h; simultaneously delete all other vertices of residual degree at most one. At most the other endpoint of a rooted path can be among the deleted vertices. Deleting those vertices therefore decreases an admissible capacity by at most one per round. Iterate; the final capacity is the remaining vertex count plus the number of rounds. This adapts the project's existing rule rather than claiming a new theorem.

3. **Whole-block chains (PROVED).** Include bridges as blocks and treat an isolated h as a singleton. Root the block-cut tree at h if it is a cut vertex, otherwise at its block. The used edges of any simple rooted path visit blocks along one outward chain: leaving a branch and returning would repeat its attachment vertex. Extend that chain to a leaf. Take the SET UNION of the WHOLE vertex sets of its blocks, including articulation vertices whose tree nodes are off the chain. The path lies in that union. Apply the parity bound to each such union and maximize over chains. Omitting an off-chain articulation is false, with an explicit Q4 counterexample in review.md and the figure.

4. **Cycle-block capacity (PROVED).** An induced path cannot occupy every vertex of a block that is itself a cycle. Along the actual used-block chain, shared articulation vertices must be selected; hence each cycle requires a distinct omitted vertex not shared with another traversed cycle. Subtract one per such cycle from the chain union size. Extending to a leaf preserves an upper bound: a new k-vertex block contributes k-1 new vertices and, if cyclic, only one extra penalty; k>=4 makes that increment positive. Take the minimum with parity. This is an induced-path rule, not a rule for unrestricted Hamiltonian paths on cycles.

5. **Small vertex separators (PROVED).** For any k-vertex set K, deleting K from a simple path leaves at most k+1 segments, each in a component of G-K. If h is outside K, its component must be included and at most k other components can be visited. Bound by k plus that root component's size plus the k largest other sizes. If h belongs to K, at most k components are needed. The implementation checks selected pairs, which limits strength but cannot invalidate the upper bound. A component may be revisited in multiple segments; replacing its capacity by its longest SINGLE path is false. review.md gives an explicit nine-vertex induced-path counterexample to that shortcut.

6. **Disjoint claw and endpoint packing (PROVED).** In any induced path, a selected vertex has at most two selected neighbors. Thus a four-vertex group consisting of a center and three neighbors cannot be fully selected. Every such group forces at least one omission. For the suffix head h, the full group A={h} union N(h) contains at most two selected suffix vertices, since h is an endpoint. It forces max(deg(h)-1,0) omissions. Remove A from the packing domain, greedily choose pairwise vertex-disjoint four-vertex claws, and sum their losses. Disjointness ensures the losses refer to distinct omitted vertices. This gives B=|R|-endpoint_loss-number_of_claws. Combine with other complete bounds by MINIMUM. Do not add claw losses to overlapping cycle losses.

7. **Memoization (PROVED).** Within an append-only run with fixed target/domain, (selected vertex set, current head) determines all forbidden future vertices through N[selected minus head]. Previously exhausted such states are interchangeable. UNKNOWN states are never recorded as exhausted. This does not apply to interior rerouting.

All proofs here are ordinary mathematical arguments with executable controls, not fresh Lean formalizations. No learned heuristic is used for irreversible pruning. Candidate ordering affects traversal only.

## Implementation and evidence

- graph_solver.py: standalone standard-library exact DFS, 512-bit masks, seven bound modes, exhausted-state memoization and explicit SAT / UNSAT_EXHAUSTIVE_PYTHON / UNKNOWN statuses. UNSAT_EXHAUSTIVE_PYTHON is not a Lean-kernel certificate.
- graph_solver_reviewed_v1.py: frozen pre-claw implementation, matching the first implementation review's source hash.
- validate.py: 1,324 Q3/Q4 graph/root cases checked against a separate exhaustive induced-path oracle, plus small-cube positive and negative search controls for every mode.
- independent_checks.py and review_implementation.py: independent referee programs; review.md gives counts and source identities. The claw update has its own hash-bound review in review_v2.json: 23,120 arbitrary-graph root cases, all 65,535 nonempty Q4 domains at a canonical root, and 12,000 independent Search controls passed.
- review.md: complete independent arguments and two unsafe-shortcut counterexamples.
- check_branch.py and check_claw_certificate.py: independently recheck the concrete Q9 branch certificates.
- global235_probe.json: 20,000 nodes, 1,710 block-only prunes, UNKNOWN.
- global235_hybrid_probe.json: 20,000 nodes, 14,207 claw prunes, UNKNOWN. These counts refer to DIFFERENT explored trees; they are not a direct speedup comparison.
- hybrid_bank152_benchmarks.json: all eight selected 152-vertex prefixes exhaust at target192. Leaf baseline totals 1,319 nodes; block 956; claw 583; hybrid 479 (63.7% fewer than leaf). These are nonrandom, small, restricted cases already covered by the existing project's longer-prefix results. They establish neither a new bank theorem nor a global bound. Single-run timings below 0.1 s are too small for a robust speed claim. The two-vertex separator mode was expensive and supplied no extra prunes in the initial ablation.

## Reproduce

From this directory, with Python 3.12+:

```sh
python validate.py
python independent_checks.py
python review_implementation.py
python review_v2.py
python check_branch.py
python check_claw_certificate.py
python benchmark.py
python benchmark_bank.py
python benchmark_hybrid.py
python graph_solver.py --n 9 --edges 235 --mode hybrid --nodes 20000 --seconds 15 --output my_probe.json
python make_figures.py
```

Only figure raster previews additionally require Pillow and a local Segoe UI font. SVG generation uses standard-library code. Bank experiments read the existing work/branch241-audit/repo/work/bank9.json fixture; it is included in the local delivery ZIP. Most checks are independent of that bank. Preserve prior result files if rerunning an experiment.

## Literature and next obstruction

Dahan, Tabib, Shimony and Felner, *Generalized Longest Path Problems*, SoCS 2022, discusses block-cut and separator heuristics, induced-path pattern bounds, overlapping components and the cost of computing those bounds:
https://ojs.aaai.org/index.php/SOCS/article/download/21752/21516/25795

This paper explicitly connects these ideas to Snake-in-the-box and earlier work by Palombo et al. (2015). Accordingly, no novelty claim is made for block decomposition or star pattern packing. What is new in this local work is its implementation, integration, concrete tested branch certificates and measured ablation in this workspace.

The obstruction to a new global bound is coverage. These lemmas eliminate individual residual states; all symmetry classes or a complete branch-and-bound cover would still need to be exhausted and independently certified. Dense residual biconnected blocks remain costly. Next work should improve disjoint pattern selection and endpoint-aware per-block bounds, with dynamic scheduling to control checking cost; only then consider full certified coverage. No existing proof checkpoint has been modified, no operating-system protection bypassed, and nothing in this round has been uploaded.

### Why a global upper-bound theorem has not followed automatically

On the entire Q9 cube, a disjoint four-vertex-claw packing can contain at most 128 groups. Thus this kind of omission argument alone cannot force more than 128 omissions from 512 vertices: even a perfect packing only gives at most 384 selected vertices. If the head's whole closed neighborhood is handled first, it occupies ten vertices and forces eight omissions; the remaining 502 vertices hold at most 125 disjoint claws. This particular root-star scheme therefore cannot force more than 133 omissions, and cannot make its root capacity smaller than 379 vertices. Both limits are far weaker than the inherited global bound. Its benefit here is conditional on a fixed prefix having already forbidden a large fraction of the cube. A new global bound still requires a complete cover of such conditioned cases, or a stronger overlapping-pattern/counting theorem with a fully justified charging argument.
