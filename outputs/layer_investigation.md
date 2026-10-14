# Testing the 196-edge hypothesis by joining two layers

The sequence-based hypothesis remains \(a(9)=196\). The following investigation tests one concrete route to a construction. It does not settle the hypothesis.

## Exact joining condition

Write a nine-dimensional vertex as \((v,b)\), with \(v\in\{0,1\}^8\) and \(b\in\{0,1\}\). Within a layer, adjacency is unchanged. Between layers, two vertices are adjacent precisely when their eight-dimensional parts are equal.

Suppose paths \(A\) and \(B\) have lengths \(r\) and \(s\). Traverse \(A\) in the first layer, cross once, then traverse \(B\) in the second layer. This is an induced path exactly when the last vertex of \(A\) equals the first of \(B\), and no other pair of their vertices is equal. Its length is

\[
L=r+s+1.
\]

The construction is discussed in [Taylor, Section 3](https://arxiv.org/html/2609.27483v1). `LayerJoining.lean` independently proves sufficiency (`join`) and necessity (`compatibility_necessary`) for an arbitrary base graph and its product with a binary edge. The file also proves the following arithmetic consequences, conditional on the known bound \(r,s\le98\):

- For \(L=196\), the lengths must be \((98,97)\) or \((97,98)\).
- For \(L=197\), both lengths must be 98.
- Every single-crossing construction has length at most 197.

The eight-dimensional universal upper bound remains a literature input. `IntegerLayerBridge.lean` now checks the injective map \(J(u,b)=u+256b\), proves adjacency preservation in both directions, and converts the general joining theorem directly into `Snake9.Snake`. Compatible paths of lengths 98 and 97 therefore produce a checked 196-edge snake; compatible paths of lengths 98 and 98 produce a 197-edge snake. No such compatible pair is asserted to exist. The module also checks the necessity of compatibility for this integer-encoded construction.

## Published seed and reproducible tests

The [Minor Triad records page](https://www.minortriad.com/snake/) provides a 98-edge example attributed to Carlson and Hougen (2010). Its transition sequence and vertices are stored in `snake8_witness.json`. `Snake8.lean` checks all 99 distinct vertices and every adjacency condition directly in the eight-dimensional cube, using kernel evaluation.

Two computational tests used this fixed example:

1. **Isometric copies.** Take a 97-edge path by deleting either endpoint of the same 98-edge example. Try both possible joining endpoints of each path, all eight-coordinate permutations, and the translation required to identify the chosen endpoints. All 322,560 placements were examined, counting equivalent placements separately. The minimum intersection had 15 vertices. A valid single-crossing join requires exactly one, so none works.
2. **Arbitrary partners.** A constraint model searched for any 97-edge eight-dimensional snake beginning at either endpoint of the fixed example and avoiding its other 98 vertices. Both instances returned INFEASIBLE. This allows arbitrary partner paths, beyond copies of the seed. Prefix truncation also excludes a longer partner beginning at the same joining vertex.

Results are recorded in `layer_search.json`; the independent implementation is in the research-code archive. The first test is exhaustive enumeration within its specified family. The second is a solver result. Neither exclusion has a Lean-checked certificate.

Small controls reproduced a 7-edge join in dimension four and excluded an 8-edge join using the corresponding fixed three-dimensional seed (`layer_controls.json`). These controls test both endpoint orientations and directly validate every pair in each constructed path.

Additional 30-second searches for partners of lengths 93, 92 and 91 at each endpoint all returned UNKNOWN (`layer_threshold.json`). Thus the best possible partner length for this seed remains unresolved. A weaker model requiring only induced degree at most two admits 106 selected vertices (`complement_relaxation.json`), so that local degree condition alone does not provide the needed exclusion.

These tests exclude a 196-edge single-crossing construction containing this particular 98-edge seed or any isometric copy of it. They leave open different 98-edge snakes and constructions that cross every coordinate more than once. There is no claim that the seed represents every optimal eight-dimensional snake.

## Implication for the hypothesis

The numerical pattern alone supplies no geometric guarantee that the two required long paths can coexist. The verified joining rule makes that missing condition explicit, and the fixed-seed searches show a concrete obstruction. Therefore 196 remains a low-confidence conjecture, with no construction and no matching upper bound. The Lean-checked nine-dimensional lower bound remains 191.
