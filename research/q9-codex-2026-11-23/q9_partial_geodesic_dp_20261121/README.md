# Partial geodesics after a half-cube translation

For each of the 131 input Q9 snakes, an axis chooses a half cube. An arbitrary nonzero translation on its other eight coordinates moves that half. Each retained original transition is replaced by a shortest path. The searched slice contains 192 edges. Either end may fall strictly inside one of the two end transitions. The integral pass handles both ends on original vertices. A 192-edge slice necessarily contains at least two original vertices because a single Q9 shortest path has at most nine edges and two partial paths through just one original vertex have fewer than 19. The two enumerations therefore cover any 192-edge subpath of such a construction. No condition is imposed on unretained parts outside the slice.

scan.cpp processes windows in order of their right endpoint. It counts all feasible endpoint-coordinate pairs using the anchor contact filter, propagates reachable subset ranks forward and backward on each full gap, then checks that all ranks across all gaps can receive distinct vertices. A failure before endpoint placement excludes every endpoint pair of that core. replay.cpp independently enumerates windows from the other end using prefix lengths, explores both gap frontiers in cube coordinates, and uses an iterative alternating-path matching. All 131 per-input counters and all surviving window identifiers and endpoint counts agree for both partial and integral windows.

complete.py encodes each surviving window once. Optional stages at the left and right cover every split of the required remaining length. Mandatory stages enforce one vertex per rank and the consecutive transition constraints. Different gap interiors cannot overlap or touch. Each vertex checks its contacts against every core anchor. timeline.py independently builds absolute time positions for each split, propagates singleton contacts, and uses MiniCard with a different positional adjacency encoding for the remaining cases. A 31-edge positive control from a real input places both ends two steps inside an edge and retains four complete stretched edges. Two separately reconstructed paths were checked point by point.

The plain CaDiCaL LRAT derivations for the 236 distinct CNFs are compressed in proofs. The checker accepts only positive RUP hints. For every added clause it negates the clause, follows the indicated unit propagation to conflict, and requires the empty clause before accepting the CNF. The generator and independent window enumerator are ordinary research code. This is a finite computation on the stated transformations and inputs.

To verify from the repository root with Python's standard library:

```sh
python3 -B q9_partial_geodesic_dp_20261121/audit.py
python3 -B q9_partial_geodesic_dp_20261121/proof.py --check
```

To regenerate the independent geometric enumeration, compile replay.cpp with C++20 and run the binary on q9_gap_generations/prior191.words. Its arguments are target length, surviving-windows output file and an optional third argument for the integral-only pass. For the position-level replay, use a Python environment with python-sat and run timeline.py tail head integral. summary.json records the row-wise checks, both SAT runs and the positive control. proof_replay.log is the successful second verification of all archived proofs.
