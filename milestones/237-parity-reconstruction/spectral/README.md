# Necessary conditions for a partial majority set

Let an induced path of length \(2k\) have even-position vertices \(v_0,\ldots,v_k\). For a subset \(U\) of these vertices, join distinct \(a,b\in U\) when some opposite-colour vertex has exactly \(a,b\) as its neighbours in \(U\). Count distinct partners even when several labels realize the same edge.

Suppose \(m\) of the \(k+1\) even-position vertices were omitted. If the resulting graph has \(I\) isolated vertices and \(L\) leaves, then

\[
2I+L\le 2m+2.
\]

The odd-position label between consecutive retained positions of the original ordering sees exactly that pair in the complete even-position set. Restriction preserves both neighbours and cannot introduce any other neighbour. Thus a retained vertex with two retained immediate neighbours in the original ordering has at least two distinct partners. A retained vertex with one retained immediate neighbour has at least one partner. Assign an isolated vertex two units and a leaf one. Its assigned units are bounded by the number of absent immediate neighbours, counting a virtual absent position beyond either end. Summing counts each omitted position at most twice and each virtual position at most once.

For \(m=0\), every vertex has a partner provided \(k>0\), and at most two vertices have only one partner. A stronger necessary condition uses vertices with at most two partners. Every such interior vertex must use both incident edges of the ordering. Therefore any neighbour of a fixed vertex that has at most two partners must be an immediate predecessor, an immediate successor, or one of the two endpoints. Five such neighbours are impossible. If two leaves already exist, both endpoints are fixed and every edge incident with a vertex of degree at most two must occur in the ordering.

The stronger condition excludes a set that passes the isolate and leaf checks. In the nine-cube take the six even vertices \(3,9,10,17,23,27\) in binary integer encoding. The complete list of labels and their two neighbours is

| Label | Neighbours |
| --- | --- |
| 2 | 3, 10 |
| 7 | 3, 23 |
| 8 | 9, 10 |
| 21 | 17, 23 |
| 26 | 10, 27 |
| 31 | 23, 27 |

The leaves 9 and 17 force the endpoints. The three neighbours 3, 9 and 27 of vertex 10 each have degree at most two. This would require three ordering edges at 10. Consequently this set cannot be the complete six-vertex majority class of a ten-edge snake.

## Directed cut for a complete majority set

Take arbitrary subsets \(S,T\) of the complete majority set \(U\). Write \(e(S,U\setminus T)\) for the number of ordered pairs of adjacent vertices whose source belongs to \(S\) and whose target lies outside \(T\). Then

\[
2|S|\le 2|T|+2+e(S,U\setminus T).
\]

From each vertex in \(S\), count the two directions along the contracted Hamiltonian ordering. At most two directions encounter the ends of the ordering. Each vertex of \(T\) receives at most two directions. Every other direction reaches a vertex outside \(T\) along one of the counted simple edges. Each ordered pair occurs at most once. The argument allows \(S\) and \(T\) to overlap.

## Proof checking

`ContractedDegrees237.lean` extracts consecutive contracted partners from an arbitrary even-length induced path, proves the endpoint rules and computes the displayed table over all 512 possible labels by kernel reduction. `PartialDeficit237.lean` proves label preservation under restriction and the summed deficit inequality using an arbitrary Boolean retention function. It imports the first module. Both use the existing round-231 definition of an induced path. The proofs concern the mathematical pruning criteria. The enumeration of candidate sets by the separate search program is a separate computation.

`Cut237.lean` proves the directed cut bound for arbitrary orderings whose successive vertices are adjacent, then applies it to the graph of distinct partners extracted from an induced path. Computing a cut on a particular labelled graph is a separate finite calculation.

Using Lean 4.19.0, put `milestones/231-endpoint-exchanges/build` and a writable build directory on `LEAN_PATH`. Compile the three modules in the order `ContractedDegrees237`, `PartialDeficit237`, `Cut237`, using `-j1 -s8192 -o <build>/<module>.olean <module>.lean`. The three logs contain the reported axiom dependencies.
