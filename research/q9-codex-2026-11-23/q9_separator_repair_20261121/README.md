# Separator- and degree-core-directed flips of the majority set in Q9

An induced 192-edge path has 97 vertices of its endpoint parity. For a proposed majority set A, its permitted graph H has A as vertices. A distance-two pair x,y is an edge exactly when one of their common opposite-parity cube neighbours has precisely x,y as neighbours in A. A Hamilton path in H lifts to a 192-edge induced cube path by inserting one such mediator per edge. Mediators for different edges cannot coincide, and mediators all have the same parity.

## Separator certificates

If a Hamilton path exists, H minus a separator C can have no more than |C|+1 components. A component K with one distinct neighbour in C additionally needs an endpoint in K: otherwise the path would have to enter and exit through the same cut vertex. A component with zero neighbours in C needs both endpoints. Every degree-one vertex must already be an endpoint. Thus, with T the degree-one vertices of H, a necessary upper bound of two applies to

`|C ∩ T| + Σ_K max(|K ∩ T|, 2 − min(2, |N(K) ∩ C|))`.

The 5,062 words of q9_three_axis.in give 2,817 distinct labelled 97-point sets. Of 273 passing the earlier connectivity, degree and forced-degree filters, 128 have a stronger certificate using one or two branching vertices. For example, zero-based row 37 has 114 permitted edges. Removing vertex 318 separates 88 vertices from 8. Both forced leaves, 492 and 500, belong to the larger component, but the smaller component needs its own endpoint. The required three endpoints exclude a Hamilton path. The saved component lists and an independent Hamming-distance-two graph reconstruction check all 128 certificates.

## Targeted exchanges and concrete outcomes

For a failed separator, select mediators connecting two of its different components. A direct new edge retains its two endpoints and drops every other old neighbour of its mediator. A second construction inserts a new majority point and creates two admissible edges through it. A third simultaneously creates two direct bridges using compatible removals. The cardinality-constrained SAT search selects the remaining drops, additions, mediators and full path. Endpoint count and all degrees are exact; disconnected cycles are cut. This differs from scoring a random interchange. The ordinary 2,816 five-/eight-point and 1,408 minimum-support families returned UNSAT. Wider families allow all compatible new vertices, and some free every old majority position outside mandatory anchors. summary.json reports solver-budget outcomes separately for the broader, mosaic and second-generation families. Instances can overlap across search stages.

Allowing a forest of short paths gave 165 distinct sets, of which 112 had connected permitted graphs. None eliminated the full original endpoint/cut obstruction. The longest actual path in these stored covers had 168 edges. These 165 sets were separately tested for a Hamilton path with no mediator restrictions in two implementations.

A separate SAT repair required both H and H−C connected with at most two leaves. It gave 159 successful assignments in broad and donor-guided partial exchanges, representing 90 distinct 97-sets. Sixty-three were absent as labelled sets from the input bank; no cube-isometry novelty claim is made. Both exact Hamilton implementations excluded all 90. For source row 4525 a seven-for-seven exchange creates bridges through vertices 236 and 110 while eliminating the separator {40,190}; the updated graph instead fails at cut {163}. A second generation used 298 directed families on 16 sets with new separators. Every family returned UNSAT.

For **all 90** repaired sets the degree-two equations alone are already infeasible on the permitted graph augmented by a single universal dummy (512). A Hamilton path would become a Hamilton cycle by joining its two ends to the dummy. Deletion-shrunk assumption cores have 6–16 vertex equations; they are inclusion-minimal relative to these degree groups. The smallest found uses real vertices 40,45,51,63,101 and the dummy. Glucose generated a DRAT proof of this reduced CNF, and independent drat-trim replay succeeded from the saved compressed trace.

The final construction tests prospective edges by adding them to the old graph and asking whether that specific degree core becomes satisfiable; only demonstrated repairs are used to generate actual swaps. All 450 target families returned UNSAT. Concrete filling constructed 258 distinct 97-sets in which the previously impossible set of degree equations is now satisfiable on the actual permitted graph. Releasing every mediator and endpoint, both exact Hamilton implementations excluded each of these 258 sets. Repairing a named obstruction therefore did not suffice to reach a 192-edge witness in this sample.

## Controls and reproducibility

The five-swap planted bridge repair and the one-swap articulation/endpoint control each restore a pairwise verified 190-edge path on 96 majority vertices. In the latter the damaged graph passes the previous necessary tests, its cut at vertex 305 requires three endpoints, and selecting mediator 274 and adding majority vertex 270 restores a valid path. The 192-edge search, the shorter controls, and the relaxed path-forest or degree-core models have distinct completion conditions.

The saved results can be checked directly from the parent workspace:

```sh
d=q9_separator_repair_20261121
python -B "$d/verify.py"
python -B "$d/check_core_moves.py"
python -B "$d/cores.py" /path/to/drat-trim --replay
python -B "$d/summary.py"
```

Source files follow the experimental stages. Use macOS clang++ with -O3 -std=c++20 and Python with python-sat including Minicard, CaDiCaL 1.9.5 and Glucose4. Run cuts.cpp with q9_three_axis.in on stdin, keeping stdout as cuts.txt. Then prepare.py writes the 128 certificates and jobs.jsonl. Run solve.py over [0,704), [704,1408), [1408,2112), [2112,2816) with a 6,500 conflict limit to create the four run*.jsonl files. broad.py narrow and broad.py wide produce deep.jsonl and wide.jsonl; retry_wide.py provides sector_retry.jsonl. small.py, concrete.py and connect_wide.py produce small.jsonl, concrete.json and connected_wide.jsonl. mosaic.py creates the mosaic donor cases and mosaic.jsonl. last.py runs with broad or mosaic and shard 0 or 1. resolved_sets.py exports the deduplicated repaired sets. Run the workspace search_q9_fixed_parity.cpp executable with --majority-sets on repairs.sets / resolved.sets, writing repair_exact.log / resolved_exact.log. second.py runs the next separator generation. cores.py creates the degree cores and first proof, then core_moves.py and check_core_moves.py generate and verify the final swaps. Run the same Hamilton executable on core_repaired.sets for the final core_repaired_exact.log. Controls come from control.py and from strong_control.cpp (prior190.words on stdin) followed by strong_control.py. Only the documented sample and bounds are covered.
