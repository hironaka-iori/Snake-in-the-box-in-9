# Forced-cycle certificate review and replay preparation

The source of forced_cycles.py and its candidate preparation were read. The separate replay_forced_cycles.py is prepared and has not been executed. No compiler, solver, scan, or software tests were run for this preparation. The current worker and its outputs were not modified.

## Mathematical review

The producer's force/delete steps are valid necessary conditions for a spanning cycle of the augmented graph:

- A vertex with two available neighbours must use both incident edges in every surviving spanning cycle.
- Once two incident edges are forced, every other edge at that vertex is excluded.
- Available degree below two or forced degree above two is impossible.
- A nonempty proper connected component of the forced graph whose vertices all have forced degree two is a closed cycle and cannot belong to a spanning cycle on all vertices.
- If deleting one vertex leaves more than one connected component, a spanning cycle is impossible, since removing that vertex from a spanning cycle would leave a spanning path.

The last certificate is called ARTICULATION by the producer, although it does not separately establish that the current graph was connected. The stated vertex-deletion condition is sufficient regardless, so this is a terminology issue rather than an invalid exclusion.

The graph has the 96 selected minority vertices and dummy vertex 512. Each exact two-neighbour opposite-colour label supplies an internal edge. Each selected vertex supported by a singleton label is adjacent to the dummy. Collapsing parallel physical labels is valid for this necessary condition. A 192-edge snake with the given complete minority class induces a spanning cycle after contracting its internal labels and connecting its two endpoints through the dummy. Therefore absence of a spanning cycle excludes that candidate minority class. No implication about other selected classes follows from a single row.

Distinct endpoint-supported vertices cannot require the same singleton label, since such a label has exactly one selected neighbour. A physical internal label has one fixed unordered pair, and cannot be used for two different edges of a simple Hamiltonian ordering. These facts explain the graph projection; the replay itself verifies finite graph construction and trace implications, without assembling this entire bridge in Lean.

## Independent replay

The replay script imports neither forced_cycles.py nor its graph builder. It reconstructs each selected class's label neighbourhoods using direct Hamming-distance comparisons against the selected vertices, then builds the augmented graph.

For every recorded force, it checks that the edge is present, is not already forced, and that the stated endpoint has exactly two currently available neighbours. For every deletion, it checks that the edge is present and unforced and that the stated endpoint has exactly two forced incident edges. Symmetric updates preserve the forced-subgraph invariant. Every terminal certificate is checked against the final reconstructed state, including exact connected components after vertex deletion and closure/connectivity of a proper forced cycle.

Every candidate class must have exactly one trace row. A valid unresolved row is recorded as unresolved and is never counted as an exclusion. A successful replay records whether all candidate classes were excluded; PASS_COMPLETE_REPLAY means all supplied rows were checked, independently of that additional Boolean.

The replay also reconstructs every candidate description from the original base, removed vertex, and inserted vertex; verifies same parity, class size, and the description's enumeration ID; recomputes exact equality groups in their recorded order; and checks all descriptions and grouped vertex lists. It matches the surviving-description IDs against zero-valued entries of the saved static decision stream. It does not reprove the reasons for the other static decisions; that is the separate exhaustive exchange audit.

All source, candidate, certificate, provenance, and replay-script input hashes are recorded and rechecked before completion. The source fingerprint in the forcing certificate must match the candidate bytes, and its producer fingerprint must match the saved producer source. Existing replay output is never overwritten. Invalid evidence produces a FAIL_REPLAY record and nonzero exit status.

## Execution and remaining scope

After the parent permits the independent replay, run the script with its default certificate data/forced-cycles.json and output data/forced-replay.json. It uses only the Python standard library, invokes no solver, and checks one candidate at a time. A custom output path is available for a later preserved retry.

Preparation inspected candidates.json at SHA-256 e3575cbb703e242fc9251509cf25637a7a94223b2371973fe243a00474e3e0b4. Its inventory contains 1,325 distinct candidate classes and 1,381 surviving descriptions. These are read inventory counts, not a completed replay result. The original-base file was read at ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b, and the static exchange result at bf75550ff4760a88713b1c469c7971e2bea75cdac3e77398d92590a7acfb60ca.

No blocking mathematical defect was found in the producer's local implications. Independent replay is still required before relying on its finite exclusions. A complete conclusion for all one-exchange descriptions requires both the separate static exclusion audit and the candidate-class certificates, with their matching provenance. This preparation establishes neither a new witness nor a global snake bound.
