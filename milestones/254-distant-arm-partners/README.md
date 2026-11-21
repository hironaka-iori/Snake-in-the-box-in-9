# Round 254 · Changing a parity class of a distant 96-edge arm

The starting eight-dimensional arm has 96 edges and endpoints 67 and 161. Its recorded sibling changes just one vertex, at position 21. For the original arm that vertex is 149. For the sibling it is 132. The previous round found a 79-edge partner at vertex 161 of the original. The question here is whether these arms, or any long arm keeping one of their parity classes exactly, can accept the 95-edge partner required for a 192-edge single-crossing snake. [Starting arms and partners](../253-repeated-segment-growth/remote-arms.json)

**Result.** None of the eight parity-preserving long arms can produce a 192-edge single-crossing join. Their maximum with an unrestricted partner is between **181 and 191 edges**. All 16 endpoints have certified upper bounds. [Root-by-root bounds and explicit joins](aggregate.json)

## Eight possible long arms

A path alternates between the two parity classes of the cube. Fix one class as a labelled set $S$ and let all other vertices and their traversal order vary. In the graph on $S$, join two vertices if some vertex of the opposite parity has exactly those two neighbours in $S$. A traversal must visit every vertex of $S$ once in this graph. Each successive pair requires one such connecting vertex. At either end, an extra vertex can be attached precisely when its only neighbour in $S$ is that end. Connecting vertices for different pairs, and the two additional endpoint vertices, are necessarily distinct. Vertices on the same side cannot form chords. These facts prove both directions of the construction. [Earlier parity criterion](../232-minority-contraction/MATHEMATICAL_NOTE.md)

The two starting arms share all 49 vertices of one parity. Their other classes have 48 vertices each and differ in one place. For each of these three choices of $S$, we enumerated every spanning path of the graph, every choice of connecting vertices and both possible endpoint attachments. The second calculation specified the endpoints first, enforced all vertex degrees by selecting edges, rejected disconnected solutions and reconstructed the labelled cube paths. Both methods give identical lists, up to path reversal. [Complete orders and cube paths](parity-families.json) · [Independent edge selection](parity-replay.json)

| Fixed parity class | Edges in the graph on that class | Spanning orders up to reversal | Labelled cube paths with 96–98 edges |
|---|---:|---:|---:|
| Shared 49 vertices | 57 | 4 | 8 |
| Original 48 vertices | 53 | 1 | 1 |
| Sibling 48 vertices | 53 | 1 | 1 |

The two singleton results are the two starting arms and already occur in the eight. All eight paths have 96 edges and represent different cube shapes. The four possible endpoint pairs are $(67,161)$, $(1,67)$, $(161,193)$ and $(1,193)$. The connecting label at the interior corner can be 132 or 149 in each case. [Path enumeration](parity_families.py) · [Independent verifier](parity_replay.py)

## Keeping the vertices while changing their order

Number the 49 shared vertices in their order along the original path, starting at index zero. Using the connection between indices 0 and 33 reverses the initial portion and replaces the original endpoint 67 by 193. Using the connection between indices 43 and 48 replaces endpoint 161 by 1. The two changes affect disjoint portions of the order. Together with the choice of label at the interior corner these give all eight arms. As unordered vertex sets they consist of 94 common vertices plus one choice from each of the pairs $\{83,209\}$, $\{17,177\}$ and $\{132,149\}$.

Four of the resulting shapes lie outside the complete 237-shape catalogue of Round 253. Each shares 96 of its 97 labelled vertices with a member of that catalogue. For every one of the four, the longest consecutive segment it shares with any of the 237 shapes is exactly **64 edges**, allowing translation, arbitrary permutation of the coordinates and reversal. The earlier construction retained 68 consecutive edges at every move. [Exchange partners and exact overlaps](rotations.json) · [Previous closure](../253-repeated-segment-growth/replay-closure.json)

## Joining into the ninth dimension

At each of the four possible crossing vertices, there are four possible parent arms. After translating the crossing to zero, their forbidden vertices are 94 common nonzero vertices and one member of each of two independent pairs. A partner is compatible with at least one of the four arms exactly when it avoids those 94 vertices and leaves at least one member of each pair unvisited. One can then choose the unvisited member for the parent in each pair. This reduces the four parent choices to two short constraints. Lean checked this equivalence and its implication for a two-layer induced path. The concrete vertex sets are supplied by the cube enumeration. [Lean argument](Family254.lean) · [Compiler receipt](Family254-compile.json)

An explicit partner of 84 edges fits the new shape `e6e522b8` at vertex 161 and gives a **181-edge join**. All 16,471 pairs of its 182 vertices have the required adjacency. The construction searched from earlier partners under both directions and all coordinate permutations, then repaired or regrew candidate paths. These constructions give lower bounds. For the original arm at 161, complete enumeration also shows that every partner retaining the first 39 edges of its saved example has at most 79 edges. [Eight new-root constructions](parity-joins.json) · [Fixed-prefix maximum and sibling improvements](constructive.json)


The 84-edge partner retains the first 31 edges of a previous 83-edge partner. With the first 37 edges retained, exhaustive enumeration instead gives a maximum of 83. The shortest prefix of that example forcing this maximum has length between 32 and 37. The original arm at root 161 now admits an 81-edge partner. For its original 79-edge partner, the shortest prefix forcing the 79-edge maximum has length between 16 and 28. [Complete prefix counts, limits and ordered paths](prefix-optima.json)

## The unrestricted 192-edge question

For a fixed 96-edge arm, a 192-edge join needs a rooted 95-edge opposite arm. A longer join can be shortened to 192 by trimming the free end. At vertices 67 and 193, the simultaneous four-parent formula already excludes a 94-edge partner. Elsewhere, individual-parent proofs and previously certified constraints complete the coverage. For the final 95-edge query, shape `2792454c` at vertex 1, two sibling exclusions force the partner to visit both original vertices 83 and 149. Omitting either would make it compatible with a sibling already known to exclude 95. The contradiction proof with these required visits replayed successfully. A separate exclusion at 94 used no such visit requirements. All 21 archived contradiction certificates are included in the round. [Family replay](family-replay.json) · [Additional family cuts](cut-replay.json) · [Individual replay](individual-replay.json) · [Forced visits](forced-caps.json) · [Forced-visit replay](forced-replay.json)

The opposite path may use any permitted eight-dimensional vertices. The positive examples were checked directly for distinctness, consecutive adjacency and absence of all nonconsecutive adjacencies. Twelve of the 16 endpoints give at most 190 joined edges. The four remaining endpoints give at most 191. The actual maximum over the eight shapes is still open. For the original arm at vertex 161, the interval for the unrestricted maximum is **178 to 188 joined edges**, corresponding to an 81-edge witness and an upper bound of 91 partner edges. [Fixed-root replay](sat-replay.json) · [Sibling replay](sibling-replay.json) · [Full 16-endpoint reconciliation](aggregate.json)

Four of the eight shapes were among the 156 unresolved shapes of Round 253. The other four enlarge that catalogue from 237 to 241. Together the two rounds exclude a 192-edge join on 89 of the 241 shapes. The remaining 152 belong to the earlier catalogue. This restriction concerns a single crossing with one fixed arm in the catalogue. It leaves the global maximum open. [Earlier classification](../253-repeated-segment-growth/README.md) · [Manuscript verification](manuscripts.json)

## Relation to the published 191-edge snakes

Round 232 already considered retaining either entire 96-vertex parity class from the saved 191-edge snakes while freely reordering it. All 145 distinct labelled classes were excluded as the minority class of a 192-edge path. Round 237 further showed that any 192-edge path must omit at least six vertices of each saved seed and introduce at least seven vertices. The calculations here apply the parity criterion to the eight-dimensional arms instead. Their opposite-face partners are free to vary. [Fixed minority classes](../232-minority-contraction/MATHEMATICAL_NOTE.md) · [Seed changes](../237-parity-reconstruction/MATHEMATICAL_NOTE.md)

The contributors have completed a new global upper bound. Their final Lean theorem supplies the two previously outstanding certificate families, and the saved standard-axiom audit passed. Together with the published 191-edge witness this gives $191\le a(9)\le230$. This round inspected the contributor’s assembly and audit. An independent rebuild of the full chain remains pending. [Contributor theorem and audit review](contributor.md) · [Published lower bound](https://arxiv.org/abs/2607.15270)
