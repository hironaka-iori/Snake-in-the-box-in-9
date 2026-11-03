# Coordinate pairs near an endpoint

This round checks geometric steps in the occurrence argument of milestone 133.
It introduces no new named mathematical definition. The proposed bound of
twelve assigned windows per endpoint remains a written result whose complete
transfer to a Lean theorem about snakes is pending.

## A common neighbour for each low-pair window

Let \(p_0,\ldots,p_m\) be an induced path in \(Q_9\), and suppose a fitting
six-transition window beginning at \(r\) has canonical sequence \(012032\).
If its two relevant counts satisfy

\[
\alpha_{r+2}+\alpha_{r+4}\le9,
\]

then one endpoint and the four vertices

\[
p_r,\quad p_{r+2},\quad p_{r+4},\quad p_{r+6}
\]

are all adjacent to one vertex absent from the snake. This statement has
passed Lean with the complete endpoint certificate from milestone 132.

In the normalized window \((0,1,3,7,6,14,10)\), the common neighbour is
vertex \(2\). Each of the seven endpoint positions supplied by the earlier
theorem is adjacent to it. Translation and permutation of coordinates transfer
these adjacencies to the original snake. The common neighbour cannot be
selected: a selected vertex adjacent to both \(p_r\) and \(p_{r+6}\) would
have to be consecutive to both in the path, which is impossible.

## One coordinate system for all windows assigned to an endpoint

Choose an endpoint, orient the path from it, and translate it to \(0\).
The same transformed path is used for every window assigned to this endpoint.
Write the first successor as \(\{b\}\). A selected coordinate pair containing
\(b\) must occur at path index two, because it is adjacent to \(\{b\}\).
There is at most one such pair.

The absent common neighbour of a window is now \(\{a\}\), where
\(a\ne b\). Its selected neighbours, apart from the possible indices zero
and two, are pairs \(\{a,c\}\) with \(c\ne a,b\). The normalization,
preservation of absence, reversal of indices, and this representation have
all passed Lean. The coordinate system is chosen once for the endpoint;
it does not change when the window changes.

## Consecutive pairs force a missing pair

Suppose \(j\ge2\), \(j+2\le m\), and three distinct coordinates satisfy

\[
p_j=\{a,b\},\qquad p_{j+2}=\{a,c\},\qquad p_0=0.
\]

Then

\[
p_{j+1}=\{a,b,c\},\qquad
\{b,c\}\notin\{p_0,\ldots,p_m\}.
\]

This is a checked theorem for actual snakes. The two possible common
neighbours of the displayed pairs are \(\{a\}\) and \(\{a,b,c\}\).
The first would be adjacent to the initial endpoint at a nonconsecutive
path position. The second is therefore forced. If \(\{b,c\}\) were
selected, the intervening triple would have a third selected neighbour.

## Counting the available coordinates and pairs

Among the eight coordinates different from the first direction, let \(A\)
be a set of \(a\) coordinates. The number of unordered coordinate pairs
with at least one member in \(A\) is

\[
7a-\binom a2.
\]

The finite identity and its partition into selected and missing pairs have
passed Lean. The proof also checks that sorted, distinct coordinate pairs
represent distinct cube vertices. This count alone does not bound the number
of overlapping windows.

For a list of distinct coordinates, let \(B\) be the available coordinates
outside \(A\), and let \(F\) contain each adjacent unordered pair having a
member in \(A\). The checked general list inequality is

\[
\text{length of the list}\le\max(1,|B|)+|F|.
\]

If the list contains an element outside \(A\), each consecutive block in
\(A\) can be counted against distinct incident edges of the list. Otherwise
the number of vertices exceeds the number of edges by one. Distinct entries
ensure that no unordered edge is counted twice. Combined with the preceding
snake lemma, this is the counting step needed for sequences of missing pairs.

That combination has also passed Lean for an actual sequence of represented
snake vertices. Distinctness of the coordinate list and absence of each
adjacent opposite pair are derived from the snake. The finite set \(F\)
must contain the relevant globally missing pairs, and the available-coordinate
set must contain the list. Their later degree-based cardinal estimates are
still explicit obligations.

## Remaining work

The occurrence proof still needs to construct the maximal intervals from
actual window starts, verify their overlap and boundary conventions, sum the
missing-degree estimates, and apply the checked arithmetic from milestone 133.
In particular, the case using all eight coordinates and the exceptional case
with five coordinates and three missing pairs must be incorporated into the
actual-snake theorem. The written estimates twelve per endpoint and twenty-four
in total must retain their incomplete Lean-checking status.

No new upper bound for snake length is established in this round. The recorded
interval remains \(191\le a(9)\le235\), with the existing limitation that the
contributor upper-bound proof has not completed its independent rebuild.
The optimum and the proposed value \(196\) remain unresolved.
