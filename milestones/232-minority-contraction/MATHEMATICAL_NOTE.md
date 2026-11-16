# Round 232: the fixed minority class

Round 231 was progress. The goal remains active; the user requests a pause after round 233.

## Exact construction criterion

Fix a 96-vertex parity class U from a saved 191-edge snake. Seek a 192-edge snake whose minority class is U. Its other 97 vertices, including both endpoints, are unrestricted.

An opposite-parity vertex with exactly two neighbours in U labels an internal edge of the contraction graph. A vertex with exactly one neighbour in U can be an endpoint label; its unique neighbour is an eligible endpoint of the contracted path. Vertices with zero or at least three neighbours in U cannot appear in the desired snake.

The desired snake exists exactly when the contraction graph has a Hamiltonian path with both ends eligible. Interleave its ordering with the two-neighbour labels, then attach singleton-neighbour labels. Labels at different ends are distinct because their unique neighbours differ. Endpoint labels differ from internal labels because the selected-neighbour counts are one and two. Same-parity nonadjacency and the exact cross-parity neighbour sets exclude extra edges. There are 96 fixed vertices, 95 internal labels and two endpoint labels: 193 vertices and 192 edges.

Conversely, deleting the two endpoints of such a snake yields that interleaving. Inducedness gives the internal two-neighbour condition and endpoint singleton-neighbour condition. No old order, crossing count, opposite-colour selection or omission bound is fixed.

Four further Lean results passed: singleton/internal label distinction, attachment of two endpoints to an actual induced path, the minority constructor, and the singleton-neighbour relation extracted from endpoints of an actual even-length path. Cube colour extraction, finite graph generation and numerical exclusions remain separate.

## Complete finite result

The 145 distinct labelled 96-sets cover both parity classes of all 131 saved seeds. Two have fewer than two eligible contracted endpoints. Another 62 have a graph leaf that cannot receive an endpoint label. The remaining 81 graphs were encoded by adding a dummy vertex connected only to eligible endpoints and requiring one circuit through every vertex. All 81 native queries returned INFEASIBLE.

An independent review reconstructs every label list, graph, dummy arc, exported model, coverage row and execution hash. No witness was found. In 33 augmented graphs, a separator S of size one or two leaves more than |S| components. A Hamiltonian cycle loses at most |S| path pieces after deleting nonempty S, so these are elementary obstructions. Twenty certificates use one removed vertex and thirteen use two. The other 48 retain native circuit evidence. The finite certificates are not Lean-certified.

## Combined conclusion

A 192-edge snake must omit at least one vertex of each parity relative to every saved seed. If it retained an entire 96-vertex seed class, that class would be either its complete minority class, excluded here, or contained in its 97-vertex majority class, excluded in round 231.

This transports to every cube-isometric copy of each seed: apply the inverse automorphism to a proposed counterexample. Inducedness, containment and parity classes up to exchange are preserved. No enumeration of isometries is needed. The statement retains its native finite-evidence qualification; it gives no global length bound or classification of all 191-edge snakes.

## Exact restricted maximum

For each saved 96-set, the longest snake whose complete selected parity class equals that set has exactly 191 edges, under the native exclusion. Alternation permits at most 97 vertices of the other parity, hence at most 192 edges. The 192-edge case is excluded and the original seed attains 191. Three additional Lean reports prove the general colour-count length bound and the strict consequence under an explicit top-length exclusion. Cube-to-count extraction, the numerical exclusion and the attaining witness remain separate evidence.

## Next constructive step

Round 233 will allow the minority class to change by one vertex, while the opposite majority class remains free. Start with 95 retained vertices and insert one new same-parity vertex. Only its nine opposite-parity neighbours change selected-neighbour counts: zero becomes one (an endpoint label), one becomes two (an internal label), and two becomes three (unusable). All other label roles remain unchanged. This permits local graph updates. The complete one-exchange search has not been performed in this round.

The maintained interval remains 191<=a(9)<=233, with the independent full rebuild of 233 pending. The contributor update through 61e6655e changes scheduling and adds no inspected completed 231 assembly. No new upper bound is claimed. Pause after the next round, 233.
