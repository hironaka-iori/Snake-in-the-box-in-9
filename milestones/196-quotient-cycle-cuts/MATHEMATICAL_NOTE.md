# Round 196: cycle exclusions in the paired-path construction

The user requested a pause after this round. Publish this checkpoint and stop; resume only upon an explicit request. No longer Q9 snake or global upper bound was obtained.

## Construction context

The goal remains a pair of 49-edge paths in one Q8 face, occupying100 vertices, and a compatible three-path forest occupying95 vertices in the other face. Four crossings would give 194 edges. The pair is sought through the safe quotient construction identified in round 195.

This round fixes the involution determined by the first saved 47-edge pair. In coordinates 0 through 7 it swaps0 with 3 and 2 with 4, then flips coordinates 0 through 5. It preserves Hamming parity. Its 128 quotient vertices represent pairs of cube vertices. A quotient edge having two possible lifts would create a square, so both endpoints of each such edge cannot be selected. There are16 such forbidden pairs in this input. The remaining selected adjacency is still evaluated in the full quotient contact graph.

## Degree relaxation and cycle exclusions

For each quotient vertex v, let x_v indicate selection and e_v indicate a path endpoint. Each quotient edge has a variable equal to the conjunction of its endpoint selections. Impose selected degree $2x_v-e_v$, with $e_v\le x_v$, exactly 50 selected vertices and exactly two endpoint flags. The decisive query leaves both endpoints free. Colour counts are25 and 25 because the quotient is bipartite. At most four of the 48 seed orbits may be omitted.

These constraints allow one path and disjoint cycles. Whenever a cycle C occurs, impose $\sum_{v\in C}x_v\le |C|-1$. A path cannot contain every vertex of C. More generally, no nonempty finite set in which every vertex has two distinct internal neighbours can be contained in an induced path: take the contained vertex with greatest path index. Both neighbours would have to occur at the unique immediately preceding position, a contradiction.

Lean checks the finite-maximum argument and this general noncontainment theorem. It also checks the actual neighbours and noncontainment of each of the three 36-vertex cycle sets used in the decisive four-omission query. The quotient adjacency in these concrete certificates is computed from the specified coordinate permutation, translation and cube-neighbour maps. Five modules pass, with eleven theorem reports. The proof source snapshots and logs of two initial elaboration failures are preserved; accepted sources contain no admitted statements.

## Results

The fixed-root four-omission query is INFEASIBLE in 7.469 seconds, without dynamic cycle cuts. The free-end four-omission query is INFEASIBLE in 51.688 seconds after excluding three 36-vertex cycles. The resulting necessary condition is that every50-vertex safe quotient path, if one exists under this involution, omits at least five of the 48 original seed orbits and adds at least seven. In the actual paired forest, this means at least ten old vertices omitted and fourteen new vertices added. Individual labelled components may exchange representatives of an orbit, so these counts must not be applied separately to each component.

The six-omission query first stopped for the free-memory reserve after 30.891 seconds. Its interrupted result is retained. The six-omission retry returned UNKNOWN after 150.062 seconds. The six-omission case remains unresolved.

The strongest recorded necessary count after this round is at least 5 omitted seed orbits and at least 7 added orbits, corresponding to at least 10 omitted and 14 added vertices in the paired forest. This is a restricted computational lower restriction, not an attained minimum. The solver's final infeasibility has not been replayed in Lean; the checked cycle cuts are separate from that missing certificate.

## Reproduction and next step

The raw initial models are retained locally and packaged in data/solver-models.zip. Reproduce a terminal model by adding its recorded dynamic_cycle_cuts to its initial model. Omitting those cuts does not reproduce the decisive free-end query. Input hashes, resource records, solver iterations and proof receipts are retained.

On resumption, inspect the six-omission result before choosing the next bound. If unresolved, change the search representation rather than repeating the same limit. Searching endpoints and replacement blocks directly in the safe quotient can avoid disconnected cycles by construction; changing to another observed paired-forest involution is also available. Any larger paired forest still needs compatible ports and opposite-face paths before it yields a longer Q9 snake. The earlier6-to-7 comparison warns that maximizing the pair alone may sacrifice this compatibility.

The archived 235 proof still awaits a complete independent rebuild. The 233/234 bounds retain their documented conditions. Whole-manuscript consistency review remains scheduled for round 200. No historical novelty is claimed for the finite-cycle exclusion principle.

Final contributor refresh: the branch advanced to 83a681dcdf592fb135d330d842092d25bd947f50, reporting 2677 of 3118 production modules. The diff is archived in milestone 196 data/contributor-final.diff; it was neither merged nor independently rebuilt.
