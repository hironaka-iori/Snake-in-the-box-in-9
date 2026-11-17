Compilation update: the final saved source passed the guarded Lean compiler. Accepted receipts are in data/. Preparation and repair status below is historical.

# Retained-vertex degree balance

Status: Lean source prepared; no compiler, solver, or tests run for this task.

The new source is lean/ExchangeBalance236.lean. It imports only Std and exports four statements. It derives the count identity by induction over a Boolean-filtered neighbour list; it does not assume that identity. The actual graph application needs a duplicate-free, complete neighbour list and the two selected-degree equations supplied by actual paths. The source does not assert that every degree-feasible selection is connected.

## Exact local identity

Let P be the old vertex set, Q the new vertex set, A = Q \ P the inserted vertices, and D = P \ Q the deleted vertices. At a retained vertex v, let e_P(v) and e_Q(v) be its old and new endpoint indicators. For paths of positive length, the induced selected degrees are 2-e_P(v) and 2-e_Q(v). Splitting the neighbour list into retained, inserted, deleted, and unselected entries gives

\[
|N(v)\cap A|+e_Q(v)=|N(v)\cap D|+e_P(v).
\]

Thus the number of added neighbours minus removed neighbours is e_P(v)-e_Q(v), with subtraction interpreted in the integers. The Lean statement uses addition on natural numbers to avoid truncated subtraction.

The four exported results are:

- retained_degree_balance: the displayed identity, derived from the neighbour filters and degree equations.
- unchanged_status_equal_counts: an unchanged endpoint indicator gives equal added and removed neighbour counts.
- endpoint_becomes_internal: an old endpoint that becomes internal has one more added neighbour than removed neighbours, and therefore has an inserted neighbour.
- internal_addition_iff_removal: at a vertex internal in both paths, an inserted neighbour exists if and only if a removed neighbour exists.

The private partition proof remains valid for lists with repetitions as a multiplicity identity. To interpret its lengths as graph degrees, the actual neighbour enumeration must have no repetitions.

## Application to a 191-edge seed and a 192-edge candidate

The seed has 96 vertices of each parity and one endpoint in each parity. Choose the candidate's 96-vertex class as minority. Its 97-vertex majority class contains both candidate endpoints. Every retained minority vertex is consequently internal in the candidate.

For each retained minority vertex that was internal in the seed,

\[
|N(v)\cap A_{\mathrm{majority}}|
=|N(v)\cap D_{\mathrm{majority}}|.
\]

If the old minority endpoint is retained, its equation instead has one extra added neighbour. In particular, that endpoint must be adjacent to a majority insertion. Summing these identities over the retained minority vertices K gives

\[
\sum_{v\in K}|N(v)\cap A_{\mathrm{majority}}|
-
\sum_{v\in K}|N(v)\cap D_{\mathrm{majority}}|
=
\begin{cases}
1,&\text{if the old minority endpoint is retained},\\
0,&\text{otherwise}.
\end{cases}
\]

This summed identity is a written corollary; it is not an additional Lean export.

The local existence implication gives a direct necessary condition for constructing the two changed parity classes. Suppose an inserted majority vertex a touches a retained internal minority vertex v. Then some deleted majority vertex d also touches v. Since a and d are distinct vertices of the same parity in the cube, their common neighbour v puts them at Hamming distance exactly two.

Equivalently, after proposing majority insertions and deletions, every seed-internal minority vertex touched by an insertion but by no deletion must itself be deleted. For a candidate with r minority replacements, there can be at most r such distinct seed-internal minority vertices. This necessary deletion demand can be counted before solving the complete degree model. Vertices affected in the reverse direction, touched by a deletion but by no insertion, also cannot remain internal. These count and distance-two consequences are written deductions from the local theorem; their finite cube enumeration is not checked by the new source.

The exact equality gives a stronger version of this filter: every seed-internal minority vertex for which the two neighbour counts differ must be deleted. Thus the number of such vertices is at most r. The old minority endpoint is handled separately by its one-extra-addition equation whenever it is retained.

For a fixed inserted majority vertex a, let K consist of the retained seed-internal minority vertices. Every member of N(a) intersect K is a common neighbour of a and some deleted majority vertex d at distance two. Two distinct same-parity cube vertices have exactly two common neighbours when their distance is two, and none at greater distance. To see this, a common neighbour differs from a in one coordinate and from d in one coordinate; the two changed coordinates must be distinct and are precisely the coordinates where a and d differ. Each of those two choices gives one common neighbour. Taking the union over the applicable deleted vertices therefore gives

\[
|N(a)\cap K|
\leq 2\,|\{d\in D_{\mathrm{majority}}:\operatorname{dist}(a,d)=2\}|.
\]

This bound is valid without asserting disjoint common-neighbour sets. Its pointwise strength is limited: a is itself selected in the candidate and has degree at most two, so its left-hand side is at most two. A positive left-hand side therefore usually imposes only the existence of a deletion at distance two. The full per-retained-vertex equalities keep more information.

There is a separate endpoint condition on the majority side. A retained seed-internal majority vertex may have zero net neighbour change if it remains internal, or one more removed neighbour if it becomes a candidate endpoint. The retained old majority endpoint may need zero net change if it remains an endpoint, or one more added neighbour if it becomes internal. Consequently the exact internal equality cannot be imposed on every retained majority vertex.

If r minority vertices and s majority vertices are deleted, the prescribed parity totals require r minority insertions and s+1 majority insertions. A restriction on r alone gives no fixed value of s.

## Limits and attempts to falsify stronger conclusions

The unconditional claim that every insertion must be at distance two from a deletion is false. For example, the induced cube path 0,1,3,7 in Q3 extends to 0,1,3,7,6. The old endpoints have opposite parities; the new endpoints are both even. The insertion 6 touches only the retained old odd endpoint 7, and there is no deletion. This verifies the necessity of the endpoint exception by direct inspection: 6 is adjacent to 7 and to none of 0,1,3.

An insertion that touches no retained internal minority vertex gives no distance-two demand from this argument. It can belong to a portion assembled entirely from new vertices, so the condition must retain its incidence hypothesis.

The balance conditions are necessary, with no assertion of sufficiency. They neither exclude disconnected cycles nor prove that a proposed selection extends to a snake. They are consequences of the full selected-degree equations already present in the degree model; adding them verbatim does not strengthen the feasible set. Their possible value is earlier filtering or choosing which deletions must accompany insertions. No runtime improvement or finite exclusion is claimed.

The source reuses the mathematical degree interpretation established in milestones/219-linear-partner/lean/Degree219.lean and the induced selected-graph interpretation reviewed in milestones/235-joint-two-exchange/logs/degree-cycle-proof.md. It needs no imports from those modules because the new argument concerns actual Boolean neighbour counts.
