# Round 201: crossings, deletions and additions between two parent paths

This round develops general proofs for dimensional constructions. It runs no new construction search and obtains no new Q9 witness or global numerical bound. Six Lean modules pass, with 24 theorem dependency reports. The geometric interpretation of the general counting identities and the complete one-deletion classification have written proofs below; their full finite-graph assembly is not yet a Lean theorem.

## 1. Exact accounting

Let P and Q be induced paths of positive edge lengths p and q in Q_n. Place them in opposite faces of Q_(n+1), after any desired cube isometry. Their layered vertex sets are disjoint even when their projections overlap. Put N=p+q+2. Delete D original layered vertices and add A vertices outside the original layered union. Assume that the induced graph on the entire final set is one nonempty path, of edge length L.

Let k count final edges across the added coordinate, b count deleted original endpoints separately in each parent, e count original within-parent edges whose two endpoints are deleted, and H count final within-face edges incident to at least one added vertex, each edge once. These counts are nonnegative integers. The assumption concerns the induced graph, including every edge between selected vertices; choosing a path through a graph with extra chords does not suffice.

The original within-face edge count is N−2. The sum of the original within-parent degrees over deleted vertices is 2D−b. An edge deleted at both ends is counted twice in this sum. Thus precisely 2D−b−e original within-face edges disappear. The final within-face edge count is

\[
N-2-2D+b+e+H.
\]

The final vertex and edge counts are L+1=N−D+A and L=N−2−2D+b+e+H+k. Subtraction gives the exact identities

\[
\boxed{k+b+e+H=1+D+A,\qquad L+k+b+e+H=N+2A.}
\]

Consequently, if p,q≤a(n),

\[
\boxed{L+k\le 2a(n)+2+2A.}
\]

This is a restriction on a specified two-parent construction. It places no bound on arbitrary snakes that lack such a representation. The proof also works in G square K2 for any simple graph G. Positive-length parents make each original endpoint's degree deficit equal to one; a singleton parent would instead contribute deficit two. A final singleton is allowed, while an empty final graph is excluded.

With no additions, H=A=0, so

\[
k=1+D-b-e,\qquad L=N-k-b-e,\qquad k\le D+1.
\]

## 2. How original overlap is removed

Write C=|V(P) intersection V(Q)|. These projected intersections correspond to an initial matching of cross-face edges. Every original cross-edge either survives or loses at least one endpoint. Each deleted vertex can destroy only one such edge, giving C≤D+k even when additions are allowed.

Without additions the surviving old cross-edges are exactly the k final crossings. Hence

\[
C\le D+k=1+2D-b-e,\qquad
D\ge\left\lceil\frac{C-1}{2}\right\rceil.
\]

For the equality case, let t count original cross-edges deleted at both ends, and let z count deleted copies outside the original projected intersection. Direct counting gives

\[
C+t+z=k+D.
\]

If C=k+D, then t=z=0. Each deletion therefore occurs at a shared projection whose opposite copy is retained. The finite Boolean-count identity and this pointwise implication pass Lean. The scalar condition C≤D+k alone is not sufficient for connectivity or inducedness.

## 3. Complete classification with one deletion

Suppose A=0 and D=1. Exchange the parents so that the deleted vertex belongs to P=(p_0,...,p_p).

If an original endpoint is deleted, b=1,e=0,k=1. The retained P' and intact Q form one induced path exactly when their projected intersection is a singleton that is an endpoint of both. The retained path P' can be a singleton. The initial overlap C is one or two.

If an internal vertex x=p_i is deleted, 1≤i≤p−1, the two nonempty surviving pieces are

\[
P^-=(p_0,\ldots,p_{i-1}),\qquad P^+=(p_{i+1},\ldots,p_p).
\]

Now b=e=0 and k=2. The result is one induced path if and only if there are

\[
u\in\{p_0,p_{i-1}\},\qquad v\in\{p_{i+1},p_p\}
\]

such that

\[
\{q_0,q_q\}=\{u,v\},\qquad
(V(P)\setminus\{x\})\cap V(Q)=\{u,v\}.
\]

Necessity: each surviving piece must connect to Q. The two crossings attach once to each piece. Every internal vertex of Q already has degree two, so these attachments use its distinct endpoints. Each attachment also uses an endpoint of its piece. Further retained projected intersections would create further crossings.

Sufficiency: orient and traverse P^−, then Q, then P^+. The displayed intersection supplies exactly the two required crossings. Original inducedness excludes within-face chords and all contacts between the two pieces. Singleton pieces require no separate exception beyond identifying their two endpoint names.

Thus C is two or three. If C=3, then x also belongs to Q. If both attachments are p_(i−1) and p_(i+1), x is adjacent to both endpoints of Q. An induced path containing a vertex adjacent to both endpoints has length two: its position must be both 1 and q−1. Consequently this attachment choice is impossible when q>2. Lean checks that general endpoint-neighbour statement.

The classification is a written graph proof. Existing joining results support its sufficiency; this round does not claim that the whole iff statement has been assembled in Lean.

## 4. What changes from dimension six to seven to eight

Using a(6)=26 and a(7)=50, a deletion-only construction of a 50-edge Q7 snake from two Q6 parents has k≤4. The saved Q7 witness has a two-crossing split with component lengths 18,24,6 and a three-crossing split. The other coordinate splits have at least five crossings. This necessary restriction alone does not prove that the two surviving face forests can be completed to suitable Q6 parents.

For a 98-edge Q8 snake obtained by deletions from two Q7 parents, L+k≤102. Thus k≤4. If k=4, equality forces both parents to have 50 edges, D=3 and b=e=0: three isolated internal omissions, with all original endpoints retained.

There is a stronger conclusion for the saved 98-edge witness. Its coordinate profiles, indexed from zero, are:

| Coordinate | Crossings | Face sizes |
|---|---:|---|
| 0 | 14 | 50,49 |
| 1 | 21 | 52,47 |
| 2 | 5 | 48,51 |
| 3 | 13 | 50,49 |
| 4 | 26 | 55,44 |
| 5 | 4 | 47,52 |
| 6 | 7 | 47,52 |
| 7 | 8 | 50,49 |

All coordinates except 5 violate k≤4. Coordinate 5 has 52 selected vertices in one face; an original Q7 parent contains at most 51 vertices. Therefore **this particular 98-edge witness cannot be obtained solely by deleting vertices from two Q7 parent paths, in any coordinate split**. This conclusion covers all cube images of this witness, since cube isometries permute coordinate splits and can exchange their two faces. It makes no claim about all optimal Q8 snakes.

CutObstruction201 checks the coordinate alternative directly from all 99 saved vertices using kernel computation. It also checks the arithmetic contradiction under the crossing and face-size bounds. Identification of these bounds with any proposed pair of parent paths is the written argument above. The source list agrees exactly with the round188 dataset; its source hash and the table are saved in data/dimensional-comparison.json.

The earlier 6-to-7 and 7-to-8 observations should therefore guide compatible face forests, without assuming that each face forest is the result of deleting vertices from a single long parent path.

## 5. Consequences for 196 edges in Q9

For two parents of length at most 98 and no additions, L=196 forces D≤1 and k≤2. There are only two size possibilities:

1. Parent lengths 98 and 97, with no deletion. Their projected intersection must be a single common endpoint.
2. Two 98-edge parents and one deletion. Endpoint deletion is the one-crossing join above. Internal deletion is exactly the two-crossing classification, with an intact 98-edge middle path and outside pieces totalling 96 edges.

In the internal case C≤3. If C=3, both attachment points cannot be the neighbours of the omitted vertex, because the intact parent has length 98. Since both endpoints of a 98-edge cube path have the same colour, a mixed attachment using one original endpoint and one newly exposed endpoint requires i odd.

Hence any placement of two 98-edge parents with C≥4 fails to produce 196 edges by deletions alone. This obstruction depends only on the overlap and degree accounting. The historical 322560-placement census aligns original endpoints; it does not automatically cover attachments at endpoints exposed by an internal deletion.

Now permit additions and require k≥4. The general bound gives A≥1. If A=1, equality forces

\[
p=q=98,\quad k=4,\quad D=2,\quad b=e=H=0.
\]

There are exactly two isolated internal omissions. The added vertex has no selected neighbour in its own face, because H=0. In a product with K2 it has only one possible opposite-face neighbour, so it must be a global endpoint of the final path. Lean checks this endpoint conclusion for an arbitrary induced path in the two-layer product, under the no-same-face-neighbour premise.

Deleting the added endpoint leaves a deletion-only 195-edge snake with three crossings. Its original overlap satisfies C≤D+k=5. If C=5, every deleted shared projection has its opposite copy retained. The new endpoint cannot attach to a vertex exposed by either deletion: its opposite-layer position would then be adjacent within its face to the retained opposite copy of that deleted neighbour, contrary to H=0. It must attach at an original parent endpoint. The overlap equality and local opposite-copy adjacency lemmas are checked; this complete geometric composition remains a written deduction.

Thus **at least two additions are necessary if both final endpoints must come from the original parents**. Without that endpoint requirement, the one-addition alternative remains possible under these necessary conditions. No example or impossibility proof for that alternative has been obtained.

## 6. Sharpness and limitations

Two copies of the Q2 path (0,1,3), with the internal vertex 1 deleted from one copy, give the Q3 induced path (0,4,5,7,3). It has D=1,C=3,k=2, showing that the bounds on k and C at one deletion cannot be decreased in general.

The Q4 induced path (0,1,9,11,15,14,6) comes from parents (0,1) and (1,3,7,6) in Q3 by adding only (6,0). It has D=0,A=1,k=2,H=0 and the added vertex is an endpoint. Both displayed induced paths are kernel-checked, including distinctness and every adjacency pair.

Connectivity cannot be replaced by edge counts and degree conditions. Taking Q3 parents (0,1,3,7,6) and (7,6), then deleting (3,0), leaves an edge and a separate square. It has two degree-one vertices, all other degrees two, and one fewer edge than vertices, yet is disconnected. The identity alone therefore cannot certify a snake.

## 7. Verification and continuation

Accepted modules: CrossingDeletion201 (10 reports), LayerEndpoint201 (1), TwoParents201 (2), EndpointGeometry201 (4), OverlapEquality201 (4), CutObstruction201 (3). Every accepted log exits successfully and reports only the permitted standard axioms; there are no accepted placeholders or native_decide calls. Failed syntax/proof attempts, their source snapshots and execution plans remain archived separately. Full geometric assembly is distinguished above from the checked list identities, endpoint lemmas and concrete computations.

The immediate theoretical question is whether two 98-edge Q8 paths admit either the exact one-deletion 196-edge construction, or the 195-edge, three-crossing predecessor required by the one-addition alternative. These routes require mutual placement and endpoint compatibility. The general restrictions are necessary and give no prediction that such parents exist.

The 13 unresolved round200 repair cases remain saved as a secondary numerical route. No case was resumed in this proof-focused round. The archived contributor upper bound 235 still awaits independent rebuilding, and the 233/234 comparisons retain their pending premises. There is no new global bound and no claim of historical novelty.

Research pauses after publication of this round, at the user's request.
