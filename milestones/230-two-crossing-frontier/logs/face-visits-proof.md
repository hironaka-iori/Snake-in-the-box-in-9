# Face visits and crossing budgets

`FaceVisits230.lean` passed the guarded Lean compiler with three standard-axiom reports. The final accepted source hash is d3a99a456f7015a30feade83d9938e80cefd0c2a26ee57de017452b2e8f493c0. Two earlier elaboration failures are retained separately; only data/FaceVisits230-audit.json records the accepted attempt. The only imported research dependency is the accepted `LayerJoining` source. The proof author ran no solver or software tests.

## Interior runs

An interior run is a maximal contiguous part of the path lying in one face, with a vertical crossing immediately before and after it. Suppose it contains one vertex with projection (x). Both flanking vertices in the opposite face then have projection (x), so they are the same vertex. This contradicts path injectivity.

If it contains two vertices, their projections (x,y) are adjacent. The two flanking vertices in the opposite face have projections (x,y), so they are adjacent as well. Their positions are separated by three path edges. Their adjacency is therefore a chord. Every interior run consequently contains at least three selected vertices.

The first accepted Lean theorem proves this using actual indexed induced pieces (p,q,r). Exact compatibility at both vertical joins supplies the equal endpoint projections. The outer pieces must be disjoint and nonadjacent, as in the already accepted two-crossing constructor. If the middle piece (q) has zero edges, its two adjoining outer vertices coincide. If it has one edge, the outer vertices are adjacent. Both contradict the separation premise. The conclusion is that (q) has at least two edges, equivalently three vertices.

This is more general than cube geometry: the argument works for the Cartesian product of an arbitrary underlying adjacency relation with a binary edge. It does not require irreflexivity or symmetry beyond the explicit hypotheses. The source proves a necessary consequence of the joining and separation premises; it does not assume that the middle run already has the desired size.

## Counting one face

Consider a path with a positive number (c) of vertical crossings. Let (r\in\{0,1,2\}) count its endpoints in the upper face. Maximal face runs alternate, and every run is nonempty. Since at least one crossing occurs, the two endpoint runs are distinct.

Let (k) be the number of upper runs. Each internal upper run meets two crossing edges; each upper endpoint run meets one. There are exactly (r) upper endpoint runs. Counting incidences gives

\[
2k-r=c.
\]

If (u) is the number of selected upper vertices, the interior-run result and nonemptiness of endpoint runs give

\[
u\geq3(k-r)+r=3k-2r.
\]

Combining the two relations yields

\[
3c\leq2u+r.
\]

The same argument in the lower face has (2-r) endpoint runs and (l) selected vertices, giving

\[
3c\leq2l+(2-r).
\]

When (c=0), both displayed crossing inequalities hold by nonnegativity. The endpoint-run count used in the positive-crossing proof should not be reused: one run can contain both endpoints, while its Boolean endpoint flag counts it only once. Handling zero crossings separately avoids this double-counting error.

## Checked components and remaining bridge

`run_vertex_budget` takes a finite list of pairs consisting of a run's vertex count and a Boolean endpoint flag. Its explicit size premise requires at least one vertex for each flagged run and at least three for each unflagged run. List induction proves

\[
3\,\lvert\text{runs}\rvert
\leq\sum_{\text{runs}}\text{size}
+2\,\lvert\text{endpoint runs}\rvert.
\]

`face_crossing_budget` combines that result with explicit endpoint-count and crossing-incidence identities. Applied to the upper run list, its anchor parameter is (r); applied to the lower list it is (2-r). The two faces' selected counts are the sums of their run sizes. No subtraction of natural numbers is needed in the Lean statements.

The actual-path-to-run-list bridge remains unimplemented. It must construct maximal face runs, prove that they partition the indexed vertices, establish alternation and the two incidence identities, and obtain the exact compatibility and outer-piece separation needed by the first theorem from the whole path's inducedness. For an interior run, its two flanking outside vertices are nonconsecutive, so the whole path supplies that separation. Restricting the path to the relevant pieces supplies their inducedness. This written argument does not constitute a checked extraction routine.

Native allowed-domain sizes can upper-bound the selected counts only after membership and injectivity are established. Such numerical data, native crossing-count exclusions, domain preprocessing, and exhaustive search coverage remain separate from these general statements. No global snake bound or new construction is claimed.
