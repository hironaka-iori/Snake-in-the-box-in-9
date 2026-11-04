# Independent review: an undominated corner forces empty squares

The proposed degree-only theorem is correct. The endpoint restriction
strengthens its conclusion by one square. The arguments below are written
mathematical proofs; this review does not claim a Lean check.

## Degree-only statement

Let S be a selected subset of Q9 such that every selected vertex has
between one and two selected neighbours. If a vertex q has no selected
neighbour, then at least four empty coordinate squares contain q.

Proof. Translate q to the zero vertex. The zero vertex is unselected:
otherwise it would violate the selected minimum-degree hypothesis. All
weight-one vertices are unselected by the hypothesis on q. Consequently,
a square through zero is empty precisely when its weight-two corner is
unselected.

Regard each unselected weight-two corner as a pair of coordinate
directions. If there are at most three such pairs, at most six of the nine
directions occur in them. Choose two distinct unused directions a and b.
The weight-two vertex with support {a,b} is selected. Its neighbours of
weight one are unselected. Any other neighbour has support {a,b,k}, with
k distinct from a,b. If this triple vertex were selected, its three
weight-two neighbours {a,b}, {a,k}, {b,k} would all be selected, since
neither a nor b occurs in an unselected pair. This would violate the
selected maximum degree two. The pair vertex therefore has no selected
neighbour, contradicting the selected minimum degree one. Thus there are
at least four empty squares. QED.

The argument actually proves that at most one coordinate direction can
be absent from all unselected pairs. This observation also analyzes the
equality case.

## Equality forces eight endpoints

Under the same degree hypotheses, suppose exactly four empty squares
contain q. Their four unselected pairs have eight incidences. At most one
of the nine directions can be absent from these pairs, by the preceding
argument. Thus exactly eight directions occur, each once: the four pairs
form a matching, and one direction c is unused.

For each of the eight matched directions a, let a' be its partner. The
pair vertex {c,a} is selected. Its weight-one neighbours are unselected.
For a selected triple neighbour {c,a,k}, with k different from a,a',c,
all three of its weight-two neighbours are selected: c lies in no missing
pair, and the only missing pair incident to a is {a,a'}. Such a triple
would have at least three selected neighbours, which is impossible.

Therefore the only possible selected neighbour of {c,a} is {c,a,a'}.
The minimum-degree hypothesis forces that neighbour to be selected.
Hence {c,a} has selected degree exactly one. The eight choices of a give
eight distinct selected vertices of degree one.

Consequently, if S has at most two selected vertices of degree one, every
undominated corner lies on at least five empty squares. This statement
requires neither connectedness nor acyclicity beyond the explicit degree
and endpoint hypotheses. Every nontrivial induced path satisfies them.

## Sharpness of the degree-only statement

The exact construction in equality_example.py chooses all weight-two
vertices except the four pairs {0,1},{2,3},{4,5},{6,7}. It also chooses all
weight-three vertices containing one of those four pairs. There are
60 selected vertices. Independent adjacency enumeration gives eight
vertices of degree one and 52 of degree two. The induced graph consists
of four three-vertex paths and six eight-cycles. At zero, the selected
neighbour count is zero and exactly four incident squares are empty.

Thus the four-square bound is sharp under only selected degrees one or
two. This construction has eight endpoints and is disconnected; it does
not show sharpness for snakes or for the endpoint-strengthened bound.

## Consequence for the rounding loss

At an undominated corner the remainder is 12 times its empty-square
count. The degree-only theorem therefore gives a contribution at least
48. With the endpoint restriction, it gives a contribution at least 60.
All remainder terms are nonnegative. Thus any nontrivial snake with total
loss at most 59 has a selected neighbour at every cube vertex. In
particular, total loss at most three forces this same property.

This reduces the low-loss case to selected sets whose open neighbourhoods
cover the cube. It does not exclude those sets, prove a positive loss
lower bound, or improve the numerical snake bound by itself.

## Scope of this review

The local proof was checked independently against the coordinate
adjacencies and all degree assumptions. The equality example was run
with exact Python integer arithmetic and no search solver. The parent
owns any Lean implementation and its separate acceptance record. No
compiler, graph worker, or nested agent was launched by this review.
