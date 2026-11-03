# Occurrences assigned to one endpoint

**Written result, not yet Lean-checked.** Let an induced path in \(Q_9\) contain fitting canonical \(012032\) windows. Count each window start once, and assign a counted window to one endpoint that is at Hamming distance two from both of its second and fourth internal centres. An arbitrary such assignment has at most

\[
W\le 11+\delta\le12
\]

windows at each endpoint, where \(\delta=1\) if a counted window has that endpoint as a window boundary, and \(\delta=0\) otherwise. Thus the bound is eleven when there is no counted boundary window. This applies in particular to windows whose pair count is at most nine, using `ActualEndpoint132.actual_pair_endpoint` to obtain the assignment. The proof below actually bounds a larger geometric class. No parity assumption is imposed on the path length, no witness attaining the bound is asserted, and this does not by itself improve a global length bound.

The earlier bound thirteen from milestone122 requires both endpoints to satisfy its distance conditions. It is not used here. The simpler proposed estimate sixteen is also valid, but the absence of certain coordinate pairs gives the stronger estimate above.

## Reduction to coordinate pairs

Orient the path from the endpoint under consideration and translate that endpoint to \(0\). Write its first two successors as \(\{b\}\) and \(\{b,c\}\). Reversal preserves the canonical direction shape \(012032\), up to relabelling, and exchanges the two centres. All counted window starts are even in this orientation, since their centres are at distance two from the endpoint.

Among selected distance-two vertices, \(\{b,c\}\) is the only pair containing \(b\). Another such pair would be adjacent to the selected vertex \(\{b\}\), in addition to its two path neighbours. The other selected distance-two vertices therefore form the edges of a simple graph on the eight coordinates different from \(b\). The exceptional pair \(\{b,c\}\) occurs only once, at path position two.

For the normalized window

\[
(0,1,3,7,6,14,10),
\]

the possible endpoint positions are

\[
0,10,18,34,66,130,258.
\]

The other seven vertices at distance two from both centres are adjacent to the internal vertex \(7\), which already has its two selected path neighbours. They cannot be selected. At each of the five endpoint positions outside the window, its four alternate window vertices are coordinate pairs with a common coordinate. At either boundary position, the other three alternate vertices are pairs with a common coordinate. These are direct calculations in the displayed window.

Call that common coordinate the anchor within this proof. It is different from \(b\), since only one selected pair contains \(b\). If a counted boundary window occurs, it is the initial window after orienting from the endpoint. Include the endpoint itself as a virtual first element with its unique anchor \(c\). This element is included only when \(\delta=1\). Each counted window is now four consecutive elements in the path sampled every two steps, all with the same anchor.

## Two counting inequalities

Take the maximal intervals of sampled positions with a common anchor that contain at least one counted window. Each has length at least four. An interval of length \(\ell\) contains at most \(\ell-3\) counted starts. Intervals with different anchors intersect in at most one position: two different coordinate pairs cannot both contain two specified anchors. Intervals with the same anchor are disjoint by maximality. The virtual endpoint belongs only to the initial interval with anchor \(c\). Consequently, if there are \(k\) intervals, their summed lengths exceed the size of their union by at most \(k-1\). This follows also by ordering the intervals: an interval can meet its predecessors only at its first position.

Assume \(W>0\). Let \(A\) be the set of anchors, let \(a=|A|\), and let \(t\) count the missing edges on the eight coordinates with at least one endpoint in \(A\). Then \(1\le a\le8\) and \(k\ge a\). There are \(7a-\binom a2\) possible edges incident to \(A\). The union of interval vertices has at most this many minus \(t\), together with the one exceptional pair and the optional virtual endpoint. Thus

\[
W\le 7a-\binom a2-t-2k+\delta. \tag{1}
\]

There is a further restriction. Suppose consecutive sampled pairs in an interval are \(\{u,v\}\) and \(\{u,w\}\). The intervening path vertex must be \(\{u,v,w\}\). The alternative intermediary \(\{u\}\) would be a second selected neighbour of the initial endpoint; the sole such neighbour \(\{b\}\) precedes all distance-two vertices. The pair \(\{v,w\}\) must be absent, since otherwise the intervening triple has three selected neighbours. Therefore the successive coordinates other than the anchor form a simple path of missing pairs. They are distinct by injectivity of the snake.

For an anchor \(u\), let \(d_u\) be its missing degree on the eight coordinates. Remove the exceptional pair and virtual endpoint when present; these can only be an initial prefix of an interval. Its remaining sequence uses at most \(t-d_u\) missing edges incident to \(A\), because an edge incident to \(u\) cannot join two of its other coordinates.

For \(a\le7\), the sequence has at most

\[
(8-a)+(t-d_u)
\]

vertices. To see this, if it includes a coordinate outside \(A\), each coordinate in \(A\) can be charged to a distinct incident edge of the sequence: divide it into maximal consecutive blocks in \(A\). An end block of length \(h\) has \(h\) such edges and an internal block has \(h+1\). There are at most \(8-a\) coordinates outside \(A\). If the sequence lies entirely in \(A\), its vertex count is its edge count plus one, and \(8-a\ge1\) supplies this last term.

Every anchor is used by an interval, and \(\sum_{u\in A}d_u\ge t\). Summing the preceding bound over all intervals, adding at most one exceptional pair and \(\delta\) virtual elements, and subtracting three per interval gives

\[
W\le k(5-a+t)-t+1+\delta \qquad(a\le7). \tag{2}
\]

The exceptional pair is counted at most once in this sum: its only possible anchor is \(c\), and it occurs at the initial sampled position. Repeated anchors only increase the total missing-degree subtraction, so replacing that subtraction by \(t\) is valid.

## Closing the count

Suppose \(W\ge12+\delta\). Put \(X=W+1-\delta\), so \(X\ge13\). For \(a\le7\), (1) and (2) imply

\[
13\le 7a-\binom a2-t-2k+1,
\qquad
13\le k(5-a+t)-t+2.
\]

The first inequality bounds \(k\le8\). Checking \(1\le a\le7\), \(a\le k\le8\), and the resulting nonnegative range of \(t\) leaves only

\[
(a,k,t)=(5,5,3).
\]

This small integer check is saved in the companion record. For \(a=8\), the first inequality forces \(k=8\) and \(t=0\). With no missing pair on those eight coordinates, an ordinary interval cannot have even two such successive pairs. Even the initial interval, after allowing the virtual endpoint and exceptional pair, cannot reach four elements. This excludes \(a=8\).

It remains to exclude \((a,k,t)=(5,5,3)\). Each anchor now occurs in exactly one interval, and there are three coordinates outside \(A\). For \(u\in A\), let \(s_u\) count its missing neighbours outside \(A\). The sequence of other coordinates in its interval has at most \(3-s_u\) available vertices outside \(A\) and at most \(3-d_u\) usable missing edges incident to \(A\). Its length is therefore at most

\[
6-d_u-s_u+\varepsilon_u,
\]

where \(\varepsilon_u=1\) only when \(s_u=3\), and is zero otherwise. When at least one outside coordinate is available, the preceding block argument gives the bound with no extra term, including a sequence lying entirely in \(A\). The extra term handles the case with no available outside coordinate.

Each of the three missing edges contributes two to the following sum, whether it lies inside \(A\) or crosses from \(A\) to its complement:

\[
\sum_{u\in A}(d_u+s_u)=6.
\]

At most one anchor has three missing neighbours outside \(A\), since these would already use all three missing edges. Thus \(\sum\varepsilon_u\le1\). Summing the five interval estimates, subtracting three for each, and allowing the exceptional pair and virtual endpoint gives

\[
W\le 5(6-3)-6+1+1+\delta=11+\delta,
\]

contrary to the assumption. This proves the stated written estimate. The case \(W=0\) is immediate.

## Verification and remaining obligations

The companion JSON pins the milestone132 theorem source, its completed compilation receipt, and the original geometric core review. The new checks are deliberately small: all 512 possible normalized endpoint positions, the seven allowed positions and their common coordinate, reversal of the shape, the finite integer reduction, and all 2,300 choices of three missing edges incident to a fixed five-coordinate set. The last check independently confirms the exceptional-case double count and its upper estimate. No solver, full transition graph, or Lean compiler was run for this review. These calculations support the written argument; they do not replace its interval and path arguments.

The remaining proof-assistant work is the transport from a snake to the selected coordinate-pair graph; the interval overlap count with its boundary convention; the missing opposite-pair lemma; the simple-path block count; and the small final arithmetic. The source theorem from milestone132 supplies an endpoint, but these occurrence-counting steps have not yet been checked in Lean. No claim of sharpness or novelty is made.

For counting all low-pair windows, choose one qualifying endpoint for each distinct start and apply the estimate to each group. Any use of the resulting budget in a charge or potential argument requires its own comparison and verification. The present review establishes no new numerical upper bound on snake length.
