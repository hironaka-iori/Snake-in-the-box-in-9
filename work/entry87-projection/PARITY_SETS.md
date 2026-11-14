# Reconstructing a snake from one unordered parity class

An induced 192-edge path has 193 vertices. Its alternating parity classes have sizes 97 and 96. Translate the path so the larger class is even. The following characterization frees the order of both classes and imposes no restrictions on the coordinates.

**Lemma.** Fix one entire class S. Form a graph on S by looking at each opposite-parity cube vertex w. If w has exactly two neighbours in S, add an edge between them, witnessed by w. If w has exactly one neighbour in S, mark that neighbour as eligible for an endpoint extension, witnessed by w.

* When S has 97 vertices, a target snake containing exactly S on this parity exists if and only if the graph has a Hamilton path.
* When S has 96 vertices, the same equivalence holds with the additional requirement that both ends of the Hamilton path are marked.

**Proof.** The successive vertices of S on a snake have a common intermediate vertex. Any third neighbour in S would be a chord. In the smaller class case, each of the two outermost cube vertices has just its endpoint neighbour in S. Conversely, choose one intermediate witness per edge of a Hamilton path. Different edges have different unordered pairs of ends, so their witness sets are disjoint. Witnesses of one-neighbour and two-neighbour type are disjoint as well. The two end witnesses in the smaller-class case must be different because their unique neighbours differ. The witnesses all have the same parity, so introduce no edges to one another. The definition of the witnesses gives exactly the required adjacencies across parities. This constructs every required vertex and checks every nonconsecutive pair.

### Entry 87 with arbitrary rearrangement

Take the even and odd sets of the indexed one-chord walk as the reference sets. Keeping just the 97 even vertices while rearranging everything else already fails: the graph has components of sizes 93 and 4. Its four-vertex component is {0, 6, 17, 18}.

Keeping only the 96 odd vertices fails for a different reason. Add a dummy vertex linked to every marked endpoint. A Hamilton path with marked endpoints is equivalent to a Hamilton cycle using the dummy. The local degree-two rule forces an inconsistency:

1. Vertices 69 and 327 have degree two, and both require their edge to 70. This leaves no edge from 70 to 22.
2. Vertex 22 now needs its edge to 28. Vertex 13 has degree two and also requires its edge to 28. Thus 28 cannot use its edge to 280.
3. Vertex 280 must use its edge to 400. Vertex 472 must also use its edge to 400. This uses both slots of 400 and excludes its edges to 406 and 436.
4. Vertex 406 must use its edge to 422. Vertex 487 also requires its edge to 422. Thus 422 cannot use its edge to 436. Vertex 436 is left with just one possible neighbour, 439, but needs two.

### Changing one member of either prescribed set

There are 97 × 159 = 15,423 one-for-one replacements of an even anchor, and 96 × 160 = 15,360 replacements of an odd anchor. All **30,783** resulting sets fail. Each test allows arbitrary reordering and unrestricted choice of the entire opposite parity. Thus in any normalized 192-edge snake **at least two members of each reference parity set must be replaced**. This gives independent obstructions on the two halves of the vertex set.

The full census lists disconnection, endpoint degree failures, degree propagation and forced proper cycles. One odd replacement (69 to 84) survived the first elementary filter and was rejected by a Hamilton-path solver. It also has an independent elementary certificate: branch on whether the edge 22--28 is included in the auxiliary Hamilton cycle. Both choices lead to a vertex with fewer than two available edges. [Degree certificate](check_parity_degrees.py) verifies both alternatives using just the degree rules.

[Graph construction](parity_skeleton.py), [replacement scan](parity_edits.py), and the four `parity-edit-*.json` result files give full coverage. To check the characterization in the positive direction, the source 191-edge bank snake restricted to its first parity has a reconstructed 191-vertex arc whose returned ordering is checked against every cube-vertex pair.

### All two-member replacements

An exhaustive second step strengthens "at least two" to **at least three on each parity**, with no restrictions on order or on the other parity. For the even set there are 58,484,016 choices of two removed and two added vertices. Exactly two of these graphs pass the initial degree conditions and connectivity. Both contradict degree two in the auxiliary Hamilton cycle. For the odd set there are 58,003,200 choices. Of these, 119 pass the degree test and 118 are connected. Elementary forced-edge rules resolve 114. The four remaining odd cases have independent branch proofs with 3, 3, 15 and 3 nodes, counting leaves and split nodes. Each leaf has an impossible degree or a forced proper cycle. The total for two substitutions is **116,487,216** distinct parity sets.

The native scan updates only the nine opposite-parity neighbour lists affected by changing one anchor. Opposite vertices with exactly two anchors support an edge, those with exactly one mark a possible endpoint. Two common neighbours of an anchor pair can witness the same graph edge, so reference counts preserve the edge while either witness remains. [Incremental scan](two_parity.cpp), [survivor verification](two_parity.py), [four small proof trees](two-parity-exceptional.json), [proof-tree generator](parity_branch_proof.py). A separate literal implementation rebuilt graphs from all vertex pairs on 1,600 intermediate states and checked the native degree counts, eligibility and connectivity. [Check](audit_two_parity.py).

Lean 4.19.0 checked the general incidence and distinct-witness implications used in the reconstruction lemma. Its three theorem reports list no axioms. The finite enumerations and degree certificates are separate from these formal implications. [Lean source](ParityWitness.lean).
