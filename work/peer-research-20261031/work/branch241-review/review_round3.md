# Independent review, round 3: real queries, global scope, and exhaustive 8-cycle cuts

## Real probe evidence

The one-centre cap-zero query produced a genuine CNF UNSAT result. I replayed its 404 RUP steps and 19,963 hints again. This is a modest fixed-window result, not a tighter numerical a(9) bound.

The initial cap-21 SAT selection has 122 vertices: five 8-cycles, 25 isolated boundary vertices, ten 5-vertex paths and one 7-vertex path. Its exact new score is 21. Consequently it is not a snake. The cap-42/63/84 examples have score 42 and two 10-cycles. These independent component and score checks are recorded in probe_independent_results.json.

## Radius extension

I reviewed the changed github_query.build(radius=4..9), its fresh variable allocation and geometric remapping. Known bank snake 67 satisfies every emitted clause at all six radii. The selected vertex variable counts are 256, 382, 466, 502, 511 and 512, and every remap is collision-free. The old local cap-21 model fails the full-radius encoding, including 25 minimum-degree clauses and 20 endpoint-budget clauses. See radius_bridge_results.json.

When radius=9, every cube vertex is represented and every selected vertex has degree one or two. The endpoint counter allows at most two degree-one vertices. After all selected cycle components are excluded, each component is a nontrivial finite path, hence contributes two endpoints. Therefore only one component can remain: a genuine induced global snake. The independent_global_snake.py checker independently tests all pair adjacencies, traverses the whole path, and checks the fixed window is consecutive.

## Checkpoint and proof-scope audit

research_loop.py correctly treats the static base as the original emitted CNF plus independently justified geometric cycle-cut clauses. Every saved cut is rechecked as a connected, induced, 2-regular cube subgraph. Such a set cannot be contained in any selected induced snake.

After an UNKNOWN slice, previously learned clauses are placed immediately after that static base, and subsequent positive RUP hints can therefore refer to the same clause IDs when the combined proof is replayed. Appending a geometric cut would change this static prefix, so the implementation correctly discards its old learned proof at that point. A fresh CNF SHA256 guards a resumed run against changes to the generated query. No erroneous reuse of a timed-out solver object occurs.

I independently reconstructed the exact base CNF, checked its SHA256, checked every full saved SAT assignment against all then-active clauses, checked cut-source membership and cut geometry, independently recomputed scores, and replayed retained learned proofs. Both saved runs passed. They remain ACTIVE after finite budgets; ACTIVE/UNKNOWN is not an infeasibility result.

The radius-four run has 27 SAT models and 145 valid cuts. The fixed centre lies in an 8-cycle in 25 models and in a 7-vertex path in two. The radius-nine run has 18 SAT models and 281 valid cuts. The fixed centre lies in an 8-cycle in 14 models and in a 7-vertex path in four. The other cycles already include lengths up to 58. Thus excluding root 8-cycles is a useful optimization but does not remove every observed obstruction.

## Complete 8-cycle enumeration: independent implementations agree

An 8-cycle in a hypercube flips every used coordinate a positive even number of times, so uses at most four coordinates. If it used at most three, its eight distinct vertices would fill a Q3, whose extra cube edges contradict inducedness. Thus an induced 8-cycle uses exactly four coordinates, each twice.

Given the first two distinct coordinate flips of the fixed three-vertex window, choose two additional coordinates among the other seven. The remaining six flips are a permutation of the multiset consisting of the first two coordinates once each and the new two coordinates twice each. There are C(7,2)*6!/(2!*2!)=3,780 candidates. Reject repeated vertices and test every pair for adjacency precisely on the cycle edges. This enumeration is complete by the preceding direction-count argument.

My cycle8_permutations.py returns 294 distinct induced cycle vertex sets for the actual window [0,1,17]. The main agent's independently implemented depth-first enumerator returns exactly the same 294-element set. The manifests include the cycle vertices and my ordered direction sequences. cycle8_crosscheck.json records exact set equality. All these cuts are therefore safe to add before the solver starts, and the count is an exact finite result rather than a guess about all long cycles.

No improved numerical snake upper bound, no final global cap-21 infeasibility, and no Lean certification is asserted.
