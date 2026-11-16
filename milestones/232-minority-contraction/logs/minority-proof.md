Compilation update: all four reports passed the guarded Lean compiler. See data/MinorityContraction232-audit.json. Preparation-time statements below are historical.

# Minority-class construction with two endpoint labels

`MinorityContraction232.lean` is source prepared for the parent's compiler run. It has four intended axiom reports. No compiler, solver, or tests were run in this preparation, and no accepted source was edited.

The accepted `ColourContraction231` and `TwoCrossings188` receipts were read. Their current source, object, and compiler-log hashes matched their `PASS` receipts. The source hashes are `d0c22bf9db3554edfae7f856e28e0de3e7718bafb2ea64e35266f4d290438aa3` and `764efb0102a2ce2d22ef0dd7e7a923958232bb5836c203e696361f42b536ef3a`, respectively. Receipt hashes are `564fea79de9a6df23f33951cf598a48e89105cdccdef24794590d2275dd4ac51` and `59f92b55528ff4adda3a9351cd0df4ef843afca8ca58a646332fb85cab83305e`.

## Exact construction

Let (u_0,\ldots,u_k) be distinct chosen vertices in one colour class. Let (z_0,\ldots,z_{k-1}) be distinct vertices in the opposite class, with

\[
u_i\sim z_j\quad\Longleftrightarrow\quad i=j\ \text{or}\ i=j+1.
\]

The accepted interleaving constructor gives an induced path of (2k) edges. Add two distinct opposite-colour vertices (s,t) whose selected-neighbour sets are exactly

\[
N(s)\cap U=\{u_0\},\qquad N(t)\cap U=\{u_k\}.
\]

Then

\[
s,u_0,z_0,u_1,\ldots,z_{k-1},u_k,t
\]

is an induced path of (2k+2) edges. The Lean constructor explicitly assumes symmetry, injectivity of both internal sequences, disjointness of the selected colour classes, nonadjacency within each class, the exact internal selected-neighbour condition, endpoint disjointness from (U), (s\ne t), the two endpoint selected-neighbour conditions, and nonadjacency of each endpoint to every internal label and to the other endpoint. In a bipartite graph the colour memberships supply the relevant disjointness and nonadjacency premises; they are left explicit in the generic source.

Endpoint labels are proved distinct from all internal labels. If an endpoint label equalled (z_j), its two incident edges to (u_j,u_{j+1}) would force both index values to equal the endpoint's unique selected-neighbour index. Those indices differ by one. `singleton_label_ne_internal` proves this contradiction without assuming the desired label distinction.

`addEndpoints` attaches singleton paths using the accepted `appendEdge` constructor twice. Its premises are stated directly for an actual induced path: both endpoint vertices are new, each has exactly the appropriate endpoint as a selected neighbour, the two new vertices are distinct, and they are nonadjacent. `minorityPath` discharges those premises from the colour-class data and the accepted interleaving. It does not assume the completed longer path is already induced.

The case (k=0) is included. There are no internal labels, and two distinct nonadjacent endpoint labels attached to the same chosen vertex give a two-edge induced path.

## Converse and scope

For an actual induced path of length (2k+2), the odd-index vertices form the minority class when the graph is bipartite and its endpoint class is designated as the other colour. `endpoint_singleton_neighbours` proves directly from indexed inducedness that the first endpoint is adjacent among these odd positions exactly to position one, and the last endpoint exactly to position (2k+1). It needs no symmetry premise because both adjacency statements use increasing path order. In an undirected graph symmetry gives the usual unordered-neighbour interpretation.

The interior subpath supplies the Hamiltonian ordering of the minority class and its degree-two labels. Deriving that restriction and all colour memberships from a literal cube path is a separate bridge; this module proves the endpoint singleton-neighbour condition and the constructive lifting under explicit internal premises. No native graph extraction or search coverage is asserted.

For a fixed minority class of 96 vertices, take (k=95). The internal Hamiltonian ordering uses 95 opposite-colour labels and yields 190 edges. Two endpoint labels give 97 selected opposite-colour vertices in total and a 192-edge path on 193 vertices. The endpoint labels may have many neighbours outside the chosen minority set. Only their complete neighbour sets inside the chosen set must be singletons.

The concrete application must establish the chosen minority set, every internal label's exact two-neighbour set, each endpoint label's exact singleton-neighbour set, the Hamiltonian ordering, and its label distinctness. A final candidate still requires independent whole-path validation. This source provides no witness, numerical exclusion, or global upper bound.
