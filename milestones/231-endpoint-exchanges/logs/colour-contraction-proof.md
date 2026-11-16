Compilation update: the saved source passed the guarded Lean compiler with four standard-axiom reports. See data/ColourContraction231-audit.json. The preparation-time statements below are historical.

# Colour-class contraction

`ColourContraction231.lean` is source prepared for compilation, with four intended axiom reports. No compiler, solver, or tests were run. It imports the accepted indexed-path structure from `LayerJoining`; the earlier joining constructors do not directly supply this alternating construction.

## Construction

Choose distinct vertices (u_0,\ldots,u_k) in one colour class and distinct vertices (z_0,\ldots,z_{k-1}) in the other. Require disjointness of the two selected classes, nonadjacency within each class, and the exact selected-neighbour condition

\[
u_i\sim z_j\quad\Longleftrightarrow\quad i=j\ \text{or}\ i=j+1.
\]

Adjacency is assumed symmetric. No restriction is placed on neighbours outside the selected vertices.

The constructor gives the actual indexed path

\[
u_0,z_0,u_1,z_1,\ldots,z_{k-1},u_k
\]

of length (2k). Its vertex map reads the even positions from the (u)-sequence and the odd positions from the (z)-sequence. Separate injectivity and disjointness give global injectivity. Same-class pairs have no edges. For a mixed pair, the exact selected-neighbour condition gives adjacency precisely at consecutive positions. These statements establish the `InducedPath` fields directly; the whole interleaving is not assumed induced. The case (k=0) gives a singleton path and requires no opposite-colour vertex.

## Converse

Take an actual induced path of length (2k). Reading its even positions as (u_i) and odd positions as (z_j) gives exactly the selected-neighbour condition above. The proposed `even_odd_adjacency` theorem proves this from the original indexed adjacency criterion, handling both possible orders of the two indices using graph symmetry.

`extracted_distinct` obtains separate injectivity and disjointness from the original path's injectivity. `same_parity_nonadjacent` proves that equal-parity positions are nonadjacent in an irreflexive undirected graph. For different positions, an edge would force consecutive indices with different parity; for equal positions, irreflexivity applies.

In a bipartite graph, starting in the chosen colour class makes all even positions belong to that class and all odd positions belong to the other, by alternation along edges. If both endpoints belong to the chosen class, the path has even length. This colour-membership and even-length extraction is a written graph argument here, rather than a new Lean colour-map theorem. The proposed Lean converse starts with an already given path of length (2k) and extracts all the graph and distinctness conditions needed by the constructor.

## Labelled multigraph interpretation

Fix a chosen colour-class set (U). Any opposite-colour vertex having exactly two neighbours in (U) determines an edge between those neighbours, labelled by that original vertex. Distinct opposite-colour vertices may give parallel edges. A simple Hamiltonian path on (U), with one such label for each edge, meets the exact neighbour condition. No endpoints need be prescribed.

A physical label cannot be reused on two different edges of a simple Hamiltonian path. Its two neighbours in (U) determine a single unordered pair. Consecutive unordered pairs in an injective vertex sequence are distinct: equality either identifies their positions directly or reverses the two positions, which would require both (i=j+1) and (i+1=j). Thus selecting labels for distinct Hamiltonian edges yields distinct labels when the graph was built from physical opposite-colour vertices with their exact two-neighbour sets. This implication is written here; label injectivity remains an explicit premise of the Lean constructor.

The exact degree-two condition concerns neighbours among the chosen (U), not total degree in the ambient cube. Opposite-colour vertices with zero, one, or more than two chosen neighbours cannot serve as interior labels for this construction with both endpoints in (U). Ignoring extra selected neighbours would admit chords.

## Application and remaining obligations

In (Q_9), a 191-edge seed has 192 vertices and 96 vertices of each parity. Keeping one chosen parity class and adjoining a new distinct vertex of that parity would give 97 chosen vertices. A Hamiltonian path in the resulting labelled multigraph would use 96 opposite-parity labels and lift to a 192-edge snake with 193 vertices. This is a construction criterion, not an existence result. The proposed source does not count the seed's parity classes or certify any chosen new vertex or native multigraph.

The concrete bridge must verify the literal chosen vertex set, the ambient cube adjacency and colour classes, each label's complete neighbour set among the chosen vertices, the Hamiltonian ordering, and label distinctness. Any resulting snake should then be independently checked as a full indexed vertex sequence. Search completeness and exclusions remain native evidence unless separately certified. No global upper bound, witness, or novelty claim is made.
