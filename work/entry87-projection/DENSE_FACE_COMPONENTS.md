# How many vertices can the two outer paths occupy?

**Two mutually nonadjacent induced paths in one eight-dimensional face occupy at most 114 vertices in total.** Consequently a 192-edge nine-cube snake that crosses a coordinate exactly twice must put at least **79 vertices** in the middle path in the opposite face. This bound applies to every such snake, with arbitrary roots and endpoints.

The local calculation counts the minimum number of components in an induced linear forest in a seven-cube. Isolated vertices count as components. For 58 through 64 selected vertices the respective minima are **10, 11, 12, 13, 14, 15 and 16**. Equivalently, at each of these seven occupancies the maximum number of edges is exactly 48. A 7-face has at most 64 occupied sites by partition into four-cubes and the eight-site four-cube lemma. For smaller populations above 51 we use the fact that at least two components are required, since one Q7 induced path has at most 51 vertices. [Four-cube lemma](PROJECTION_BALL.md#the-middle-arm-must-have-65-through-99-vertices), [seven-cube path maximum, Table 1](https://plouffe.fr/OEIS/archive_in_pdf/kochut.pdf).

## From seven-face counts to the eight-face bound

Let the two outer paths together have m vertices. They have m−2 edges. Sum the component counts of the induced graphs on the sixteen seven-dimensional faces. Each vertex belongs to eight faces and each edge to seven, so the sum is

    8m − 7(m−2) = m+14.

Along a single path, cut its vertex sequence into maximal runs on each side of a coordinate. Each run is one face component because the path is induced. The runs alternate sides, so their counts differ by at most one. Two mutually nonadjacent paths contribute disjoint components, and their combined counts differ by at most two. This also covers a path consisting of a single vertex.

Suppose the two paths use 115 vertices. On every coordinate split, one seven-face contains at least 58 vertices. Its component count is at least ten throughout the possible range of 58 to 64. The opposite seven-face must then contain at least eight components. All sixteen faces together would contribute at least 8×18=144 components, whereas the identity gives 115+14=129. This excludes 115. Any larger pair of paths can be shortened to 115 vertices while keeping both components nonempty. Subtraction from 193 now gives the middle bound of 79. The arithmetic verifier also checks every excluded occupancy separately. [Component counts, witnesses and calculation](face-component-bound.json), [witness and bound verifier](face_component_bound.py).

## Exhaustion of the small cube geometries

Each split of a base cube into two halves picks a subset on each side. Horizontal edges are determined by those subsets. At a shared address there is one additional vertical edge. Thus a vertex already of degree two in either half cannot occur in the other. After this test, joining two linear forests gives a graph of maximum degree two. If the halves have c and d components and overlap at h addresses, the predicted component count for an acyclic join is c+d−h. A direct traversal checks that count and detects cycles.

The program starts by testing the 65,536 literal four-cube subsets. It builds all required labelled five-cube sets by joining opposite four-cubes. For occupancies 16, 15 and 14 it finds 1,772, 52,832 and 637,440 sets. For the corresponding six-cube occupancies 32, 31 and 30 it finds 4,454, 142,528 and 3,340,064 sets. Coordinate flips and adjacent coordinate swaps generate all hypercube isometries. One half can be normalized by this group, since the other half is tried in every placement.

For a seven-cube with 64−t occupied sites, one six-dimensional half has deficiency at most floor(t/2) from 32. Fix that half up to isometry. For deficiency three it suffices to normalize one of its five-faces and quotient the other by its stabilizer; the resulting 9,968 representatives may repeat some classes. Construct the opposite six-dimensional half from two five-cubes, each constructed from two four-cubes. The join rejects forbidden degree increases and tests the full seven-cube for cycles. This construction lets the opposite half vary over every compatible placement. For occupancies 62 through 64, a separate direct join of the labelled six-cube catalogues gives the same answers. For every reported optimum, the vertex witness is independently verified as an induced linear forest of the stated size and component count. [Enumerator](near_full_faces.cpp), [completed census](near-full-seven-dense.txt).

An additional direct enumeration of every half-full linear forest records all 17,714 labelled eight-cube solutions. Their component counts are 32, 48, 64 or 128. The degree-two filter and a literal traversal suffice for this enumeration, which uses no isometry reduction. [Program](maximum_face_forests.cpp), [counts by dimension](maximum-face-forests.txt).
