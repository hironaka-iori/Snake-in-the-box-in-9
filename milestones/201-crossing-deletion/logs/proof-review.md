# Round 201: deletion and crossing proof review

Read-only theoretical review, 13 November 2026. No numerical searches, tests, proof compilation or manuscript edits were performed. Only this report was written.

## Verdict and definitions

The proposed identity and inequalities are correct. There is a stronger exact length identity, a necessary-and-sufficient classification with one deletion, and a valid extension allowing additions. The corrected one-addition equality alternative supplied by the parent agent is also correct.

Let two positive-length induced paths have ordered vertices

\[
P=(p_0,\ldots,p_r),\qquad Q=(q_0,\ldots,q_s),\qquad r,s\ge1.
\]

Place them in opposite faces of \(Q_{n+1}\), and put \(N=r+s+2\). Delete \(D\) vertices from these two **layered copies**, add none initially, and assume the induced graph on every retained vertex is one nonempty path.

- \(b\) counts deleted original endpoints, separately in each layered copy.
- \(e\) counts original **within-parent** edges with both endpoints deleted; it excludes cross-layer edges.
- \(C=|V(P)\cap V(Q)|\) counts initial projected intersections, equivalently initial cross-layer edges.
- \(k\) is the number of retained cross-layer edges, hence the number of crossings in the final induced path.
- \(L=N-D-1\) is the final length.

The original positive-length assumption ensures an endpoint has within-parent degree one. The final path may be a singleton, although the intended application is nontrivial. The argument works for two paths in any graph product \(G\square K_2\); the cube maximum enters only in the size bound.

## Exact deletion accounting

The initial within-face edge count is \(N-2\). Summing original within-parent degrees over deleted vertices gives \(2D-b\). An edge with both endpoints deleted is counted twice, so precisely \(2D-b-e\) original within-parent edges disappear. The retained within-face count is therefore

\[
N-2-2D+b+e.
\]

Adding the \(k\) cross-layer edges and equating to the final path's \(N-D-1\) edges gives

\[
\boxed{k=1+D-b-e,\qquad 0\le k\le D+1.}
\]

The \(C-k\) destroyed original cross edges form a matching. Each needs a deleted endpoint, and one deleted copy belongs to at most one such edge. Hence

\[
\boxed{C\le D+k=1+2D-b-e.}
\]

More precisely, let \(z\) count deleted copies whose projection was outside the initial intersection and \(t\) count original cross edges with both endpoints deleted. Then

\[
D=C-k+t+z,
\qquad C=1+2D-b-e-t-z.
\]

Eliminating \(D\) also gives the stronger length statement

\[
\boxed{L=N-k-b-e=r+s+2-k-b-e.}
\]

For \(r,s\le a(n)\), this yields

\[
\boxed{L\le2a(n)+2-k-b-e\le2a(n)+2-k.}
\]

Other useful necessary consequences are

\[
D\ge\left\lceil\frac{C-1}{2}\right\rceil,
\qquad L\le N-1-\left\lceil\frac{C-1}{2}\right\rceil.
\]

These statements also hold when one retained layer is empty. If both layers retain vertices, connectivity additionally requires \(k\ge1\). None of these inequalities is sufficient for a construction.

## Exact one-deletion classification

With \(D=1\), one has \(e=0\). Exchange the layers if necessary so that the deletion is in \(P\).

**Endpoint deletion.** Here \(b=1\), \(k=1\), and the retained part \(P'\) is a nonempty path, possibly a singleton. The retained graph is an induced path if and only if

\[
V(P')\cap V(Q)=\{u\},
\]

where \(u\) is an endpoint of both paths; the sole vertex of a singleton serves as its attachment. Necessity follows from connectivity and the degree bound. Sufficiency is the existing single-crossing joining criterion. The initial overlap is \(C=1\) or \(2\), according as the deleted projected vertex is outside or inside \(V(Q)\).

**Internal deletion.** Delete \(x=p_i\), with \(1\le i\le r-1\), leaving

\[
P^-=(p_0,\ldots,p_{i-1}),\qquad P^+=(p_{i+1},\ldots,p_r).
\]

Both pieces are nonempty, and either may be a singleton. They are disjoint and nonadjacent because \(P\) was induced. Now \(b=e=0\), \(k=2\).

The retained graph is an induced path if and only if there are

\[
u\in\{p_0,p_{i-1}\},\qquad v\in\{p_{i+1},p_r\}
\]

such that

\[
\boxed{\{q_0,q_s\}=\{u,v\},\qquad
\bigl(V(P)\setminus\{x\}\bigr)\cap V(Q)=\{u,v\}.}
\]

Duplicate endpoint names in singleton pieces describe the same choice. The two pieces are disjoint, so \(u\ne v\).

Necessity: each retained piece must connect to \(Q\). There are exactly two cross edges, so each piece gets one, attached at an endpoint. Every internal vertex of intact \(Q\) already has degree two, so its cross edges use its two distinct endpoints. Additional retained intersections would be additional cross edges.

Sufficiency: traverse \(P^-\), then \(Q\), then \(P^+\), orienting each piece appropriately. The displayed intersection gives exactly the two intended crossings; the original inducedness excludes within-face chords and contacts between the pieces. Every retained vertex is traversed.

Equivalently, the original intersection is exactly \(\{u,v\}\) or \(\{u,v,x\}\). Thus \(C=2\) or \(3\). There are at most four attachment choices, choosing an original or newly exposed endpoint on each piece. The two ports need not both be immediate neighbours of the deletion.

One further restriction is useful. If \(C=3\) and both ports are \(p_{i-1},p_{i+1}\), then \(Q\) contains the deleted projection \(x\), adjacent to both of its endpoints. Inducedness forces \(Q=(p_{i-1},x,p_{i+1})\), up to reversal, so \(s=2\). Therefore, for \(s>2\) and \(C=3\), at most one port can be an immediate neighbour of the deleted vertex.

## Application to 196 edges

For two 98-edge parents, \(N=198\). A 196-edge result has 197 vertices, forcing \(D=1\).

- An original endpoint deletion gives \(k=1\), \(C\le2\), and the usual join of lengths 97 and 98.
- An internal deletion gives \(k=2\), \(C\le3\). At index \(i\), the retained pieces have lengths \(i-1\) and \(97-i\), summing to 96; intact \(Q\) has length 98. The exact three-component construction has lengths \((i-1,98,97-i)\), with two crossings.

In the internal case, \(C=3\) rules out using both newly exposed endpoints as ports, since intact \(Q\) has length 98 rather than 2. Cube parity gives an additional filter: the two mixed attachment choices, using one original endpoint and one deletion neighbour, require \(i\) odd, because the endpoints of a 98-edge path have the same colour.

Consequently, any fixed placement of two 98-edge parents with \(C\ge4\) is excluded from producing 196 edges by deletions alone, regardless of crossing count. At least two deletions are necessary and the length is at most 195.

More generally, two parents of lengths at most 98 can produce 196 edges by deletions alone only through no deletion from lengths 98 and 97, or one deletion from lengths 98 and 98. The first has one crossing; the second is classified above. Three or more crossings are impossible in this construction family at length 196.

The historical 322560-placement truncation census is not automatically a full overlap census for the two-crossing case. It aligns chosen original joining endpoints, whereas internal deletion can attach at newly exposed endpoints. Its use here requires a separate coverage argument.

## Extension allowing added vertices

Now allow \(A\) added vertices outside the original two layered parent copies. Keep \(D,b,e_D\) as above, with \(e_D\) denoting deleted within-parent edges. Let \(H\) count final within-face edges with at least one added endpoint, counting each edge once. Assume the entire final induced graph is a nonempty path.

The retained old within-face edges are still \(N-2-2D+b+e_D\), and the final edge count is \(L=N-D+A-1\). Adding \(H\) and the crossing count \(k\) gives

\[
\boxed{k+b+e_D+H=1+D+A,}
\]

\[
\boxed{L+k+b+e_D+H=N+2A.}
\]

Therefore

\[
\boxed{L+k\le2a(n)+2+2A.}
\]

The initial-overlap inequality \(C\le D+k\) still holds, since surviving original cross edges are a subset of the final cross edges. For an exact version, if \(k_A\) counts final cross edges incident to at least one addition, then \(C=k-k_A+D-t-z\).

For \(n=8,L=196,k=4\), the bound gives \(A\ge1\). If \(A=1\), equality is necessary throughout:

\[
N=198,\qquad b=e_D=H=0,\qquad D=2.
\]

Thus both original parents have length 98 and the two omissions are internal and nonadjacent within either parent. The sole added vertex has no final within-face neighbour. It has at most one cross-face neighbour, so connectivity of the nontrivial final path forces it to be a global endpoint. Deleting that new endpoint leaves a deletion-only 195-edge snake with three crossings and two isolated internal omissions.

Accordingly, **\(A\ge2\) follows if both final endpoints are retained original vertices**. Without that hypothesis, the one-addition equality alternative remains possible by these equations; its existence is not established.

For \(n=7,L=98,k=4,A=0\), equality forces \(N=102\), both parent lengths 50, \(b=e_D=0\), and \(D=3\): three isolated internal omissions. The displayed 98-edge witness's cut with face sizes 52 and 47 cannot be in this two-parent deletion family, because a single Q7 parent has at most 51 vertices. This is a useful limit on the interpretation of the theorem.

## Counterexamples and corner cases

The small examples below follow directly from their displayed vertex lists; no enumeration was run. Integers encode cube vertices, and the second coordinate of a pair is the layer.

1. **One deletion can have \(C=3,k=2\).** Take both Q2 parents to be \((0,1,3)\), delete \((1,0)\), and retain
   \[
   (0,0),(0,1),(1,1),(3,1),(3,0).
   \]
   This is an induced four-edge path, with \(D=1,b=e=0,C=3,k=2\). It refutes either strengthening \(k\le D\) or \(C\le2\) at one deletion, and attains the stated bounds for \(a(2)=2\).

2. **Counts and path degrees are insufficient without connectivity.** In Q3 take \(P=(0,1,3,7,6)\), \(Q=(7,6)\), and delete \((3,0)\). The result is the edge on 0 and 1 in layer zero plus the square on the two copies of 7 and 6. It has exactly two degree-one vertices, all others degree two, and one fewer edge than vertices. It also has \(D=1,C=k=2\), satisfying the accounting identities. It is disconnected because both crossings attach to the same retained piece.

3. **Ignoring a chord invalidates the statement.** Two copies of the edge \((0,1)\), with no deletion, induce a square with two cross edges. Selecting three of its edges as a spanning walk does not produce a snake; the fourth edge is a chord. The requirement concerns the entire retained induced graph.

4. **The deletion-only identity fails when additions are silently allowed.** In Q3 start from \(P=(0,1)\), \(Q=(1,3,7,6)\), add only \((6,0)\), and retain
   \[
   (0,0),(1,0),(1,1),(3,1),(7,1),(6,1),(6,0).
   \]
   This is an induced path with \(D=0,k=2\). It satisfies the additions identity with \(A=1,H=b=e_D=0\).

5. **Original singleton parents require degree deficits.** Let the first parent be \((0)\), the second the edge \((0,1)\), and delete the singleton. If a singleton is counted as one endpoint, then \(D=b=1,e=0\) but the retained path has \(k=0\), whereas the proposed formula gives 1. Generalize \(b\) to the sum of \(2-\deg(v)\) over deleted original vertices, giving a singleton weight two, or retain the positive-length-parent hypothesis.

6. **Empty retained layer versus empty retained graph.** Deleting an entire positive-length parent leaves \(k=0\), and the identity remains valid. Deleting both edge parents completely gives \(D=4,b=4,e=2\), whose right side is \(-1\). A nonempty final path is essential. A final singleton still has edge count \(N'-1=0\), so it is covered.

## Relation to the manuscript and limits

This is an additional explicit theorem and target classification in the current construction discussion, derived from existing elementary ingredients. No historical novelty claim is supported or needed.

- Round 190 / `sec:exchange-balance` counts omitted and added edges when replacing one path by another with fixed endpoints. It does not state the layer-crossing identity.
- Round 192 / `sec:moving-endpoints` supplies the endpoint-deficit argument used for \(b\).
- `thm:join` already covers the one-endpoint-deletion case.
- The three-path joining proposition in `sec:dimensional-constructions` gives sufficiency in the internally deleted case. The present proof also derives necessity and restricts the possible attachments.
- Round 200 / `sec:repair200` uses \(C\le D\) for disjoint final projections and a separated two-path forest. For one connected snake, \(k\) intersections remain as crossings, giving \(C\le D+k\) and the new coupling to the deletion count.

Useful consequences are solver-independent restrictions for this parent family, the exact one-deletion criterion, and the equality alternatives when four crossings and additions are allowed. They give no new Q9 witness or global bound.

Sources read in full: `milestones/190-exchange-constraints/MATHEMATICAL_NOTE.md`, `milestones/192-moving-ports/MATHEMATICAL_NOTE.md`, and `milestones/200-overlap-repair/MATHEMATICAL_NOTE.md`, all under `E:/Snake-in-a-box/`. Also read current main-manuscript lines 6376–6473 and 7737–7803, plus targeted construction/overlap search excerpts. The prior round-200 review had already read all construction and experiment sections; it was used only to locate the current statements.

This is a written proof review, not a Lean receipt, numerical census or external literature review. The parent agent controls proof integration and the requested pause after round 201.
