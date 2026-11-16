# Round 231: contract one parity class

Round 230 was progress: it closed a selected two-block family. The goal resumed on 16 November 2026. The user now requests completion of rounds 231, 232 and 233, followed by a pause. This round remains active at its publication checkpoint.

## Construction hypothesis

An extension may become possible when the entire ordering and the opposite parity class can change. Take a 96-vertex parity class from a saved 191-edge snake and add any new vertex of the same parity. Search for a 192-edge snake whose 97-vertex majority class is this set. No old path order, endpoint, coordinate-crossing count, omission bound or replacement interval is fixed.

## Exact graph reduction

Let U be a nonempty set of vertices from one parity class of a cube. For each vertex z of the opposite parity having exactly two neighbours in U, put an edge between these neighbours and label it z. Parallel edges may occur. An induced path with both endpoints in U and with U as its complete vertex set of that parity exists if and only if this graph has a Hamiltonian path.

For the forward direction, alternate positions of the induced path give an ordering of U. Each intervening vertex has exactly its predecessor and successor as neighbours in U; another selected neighbour would be a chord. These intervening vertices therefore give the labelled edges of a Hamiltonian path.

Conversely, interleave the Hamiltonian order with its edge labels. No label repeats: a physical label has one fixed unordered neighbour pair, and a simple Hamiltonian path cannot use that pair twice. Vertices from the same parity class are nonadjacent. Across the two classes, the exact-neighbour condition permits only consecutive pairs. Thus the interleaving is an induced path of 2|U|-2 edges. Collapsing parallel edges preserves Hamiltonian-path existence; any one available label for each chosen edge gives the same selected-neighbour relation.

Four Lean results passed: the actual induced-path constructor, recovery of the exact even/odd adjacency pattern from an actual even-length induced path, extracted injectivity/disjointness, and nonadjacency of same-parity positions. The concrete cube-parity extraction, finite graph generation, label choice and search evidence remain separate from these checked indexed statements.

## Complete finite survey

All 131 saved 191-edge seeds were independently rechecked. Their 262 parity classes yield 145 distinct labelled 96-vertex sets. Each has 160 possible same-parity additions. The 23,200 descriptions yield 23,127 distinct 97-vertex sets and 73 exact duplicates. This grouping uses literal vertex-set equality, without claiming classification under all cube symmetries.

The associated simple graphs have these outcomes:

| Outcome | Distinct sets |
|---|---:|
| An isolated vertex | 17,271 |
| More than two vertices of degree one | 5,807 |
| Survive the initial screen | 49 |

A Hamiltonian path cannot contain an isolated vertex in a graph of this size, and every degree-one vertex must be one of its two endpoints. The 49 remaining graphs were each searched by adjoining a mandatory dummy vertex and imposing one directed circuit through all 98 vertices. Removing the dummy is exactly a Hamiltonian path in the original graph. All 49 native queries were INFEASIBLE. No 192-edge witness was found.

An independent review reconstructed every graph, all static exclusion certificates, every circuit arc and variable, all coverage rows and their saved hashes. The solver contradictions remain native; no end-to-end Lean certificate is claimed.

## Elementary separator explanations

Deleting a set S from a Hamiltonian path leaves at most |S|+1 nonempty path pieces. Therefore its graph cannot have more than |S|+1 components after deleting S. Saved separators of size one or two explain 34 of the 49 cases.

If the graph has exactly two leaves, they must be the Hamiltonian endpoints. Deleting e of those endpoints reduces the maximum number of remaining pieces to |S|+1-e. Also, if there are exactly |S|+1 components and both endpoints survive in the same component, that component needs two path pieces: the first and last pieces cannot be the same piece when S is nonempty. This again exceeds the budget. These refinements explain another eleven cases.

All eleven additional certificates use the common surviving component of the two endpoints; none uses endpoint deletion. The remaining four graphs have no recorded certificate from these searches. A separate search for three disjoint regions each attached through one outside vertex found none for those four. No conclusion follows from that absence; their native circuit exclusions remain the supporting evidence. The 45 positive graph certificates are recorded explicitly and have written combinatorial proofs, without claiming Lean verification of their finite extraction.

## Scope and continuation

The completed exclusion covers a 192-edge candidate whose 97-vertex majority parity class contains an entire 96-vertex parity class of any saved seed. It does not cover a candidate that fixes the 96-vertex minority class while replacing its other class. That is the next construction case for round 232. In that case, internal opposite-colour vertices still represent edges, while endpoint vertices must have exactly one neighbour in the fixed class. The Hamiltonian path must end at vertices admitting those endpoint labels.

If both fixed-class variants are excluded, any successful 192-edge construction must change both parity classes relative to every saved seed. This stronger statement is conditional on completing the minority-class case; it is not a conclusion of round 231.

The global interval remains 191<=a(9)<=233. The newly inspected contributor revision 5309471b80154eff6f9a247a8edb0e865403d9f7 contains a chain targeting 231 with arithmetic 4763m<=1104764, but the inspected sources retain plain/H8, share, contextual-refutation and floor premises. No completed unconditional 231 final assembly or audit was found in the bounded review. The existing independent full rebuild qualification for 233 remains. Coworkers continue that upper-bound work.
