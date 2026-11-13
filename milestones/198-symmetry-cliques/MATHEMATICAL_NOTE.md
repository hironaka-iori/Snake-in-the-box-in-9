# Round 198: the structure of the chosen symmetry quotient

## Result and scope

The chosen symmetry gives a concrete pair of separated 47-edge paths in Q8. Their cross-distance distribution differs from every one of the 36 face forests saved in round 195, so this candidate is inequivalent to those forests under cube isometries. A search for a compatible opposite face producing 192 edges remains UNKNOWN after 120.047 seconds. No longer Q9 snake or improved global bound has been obtained.

The quotient has eight disjoint K4s, exactly 32 triangles, and exactly three vertex orbits under its graph automorphism group. Thus an unrestricted quotient-path search needs only three endpoint representatives. The proof and the necessary restriction on seed-dependent searches are given below. The completion record states the current Lean verification status separately from the written deductions and native computations.

## Eight cliques and all triangles

Use coordinates 0 through 6 and let h exchange 1 with 4 and 3 with 6, then translate by 126. The quotient G has ordinary Q7 edges together with $x\leftrightarrow h(x)$. The corresponding Q8 map is $g(y,b)=(h(y),1-b)$, with minimum displacement three; there are no loops or double-lift edges.

The displacement of h is

$$d_{\mathrm H}(x,h(x))=2+2\mathbf 1_{x_1=x_4}+2\mathbf 1_{x_3=x_6}.$$

The fixed-coordinate flips 2 and 5 contribute two. A swapped pair contributes zero when its bits differ, and two when they agree, because both translation bits on that pair are one.

A triangle in G uses exactly one h-edge. It cannot use no h-edge because Q7 is bipartite, and two edges of the matching cannot share a vertex. Its h-edge endpoints therefore have ordinary Hamming distance two. This is equivalent to

$$x_1\oplus x_4=1,\qquad x_3\oplus x_6=1.$$

Fixing these four coordinates and coordinate 0, then varying coordinates 2 and 5, gives a Q2 square with both diagonals supplied by h. Hence it is a K4. There are eight such disjoint cliques, and every triangle belongs to one of them. Each clique contributes four triangles, giving 32 in total. The explicit native census agrees with this argument.

An induced path contains at most two vertices of each K4: three would be a triangle. The triangle noncontainment follows from the finite-cycle principle checked in round 196. New concrete triangle facts and Boolean occupancy arithmetic are supplied in this round's proof files; accepted receipts distinguish completed checks from pending files.

Coordinate 0 is unaffected by h, so G is the Cartesian product of one edge with a 64-vertex graph. Each K4 is paired with its translate by 1. A path can use at most one coordinate 0 edge within such a pair of cliques: two would force a four-cycle. This restriction follows from the full square cuts already used in the search and is not an additional independent numerical bound.

## Exactly three endpoint classes

Let k be the number of equal-bit pairs among(1,4) and(3,6). The set of triangle vertices has k=0. Every graph edge changes k by at most one; matching edges preserve it. Flipping one coordinate in each equal-bit pair reaches k=0 in exactly k steps. Therefore the graph distance to the triangle vertices is exactly k.

The following symmetries preserve G: translation by any of 1,4,32,18,72, and the coordinate permutation exchanging the two swapped pairs, namely(1 3)(4 6). These generate a 64-element subgroup. The paired translations change the common orientation in each coordinate pair while preserving whether its bits agree; the three fixed-coordinate translations change the remaining bits freely. The pair exchange interchanges the two possibilities when exactly one pair agrees.

These operations act transitively on each class k=0,1,2. The class sizes are 32,64,32, and representatives can be chosen as 10,2,0 respectively. A graph automorphism cannot mix the classes because distance from the triangle vertices is intrinsic to G. These are therefore the exact three vertex orbits, even though the displayed subgroup need not be the full automorphism group.

For any induced quotient path, apply a symmetry carrying its first vertex to the corresponding representative. Length and inducedness are preserved. Consequently, unrestricted searches with first endpoint 10,2,0 cover every possible 50-vertex quotient path. A fixed-seed overlap requirement does not survive this reduction unless the seed requirement is transported along with the symmetry.

## Connected extension search and the concrete pair

The search starts from the 46-vertex direct subpath at positions 5 through 50 of the earlier Q7 seed, in each orientation. At each step, every unused neighbour of the current endpoint that avoids all earlier vertices' neighbourhoods is tried. This maintains one induced path throughout. The data specify each retained prefix and node/time limit.

| Retained prefix vertices | Orientation | Search nodes | Status | Largest quotient path found, vertices |
|---:|---|---:|---|---:|
|38|forward|16|EXHAUSTED|46|
|38|reverse|29|EXHAUSTED|47|
|26|forward|175|EXHAUSTED|46|
|26|reverse|159|EXHAUSTED|48|
|18|forward|447558|EXHAUSTED|46|
|18|reverse|31252|EXHAUSTED|48|
|12|forward|7237632|TIME_LIMIT|45|
|12|reverse|7880704|TIME_LIMIT|47|

For the 18-vertex prefixes, the maxima 46 and 48 are exact within the respective fixed-prefix extension families. The 12-vertex cases stopped after about 35 seconds each and yield no upper restriction.

The 48-vertex quotient path found from the reverse 26-vertex prefix uses only ordinary Q7 steps. Thus it lies wholly in one representative face, and its image under g lies wholly in the other. The first Q8 path starts at 63 and has transition sequence

```text
42104260210430240530421043024056042153124012310
```

The second starts at 137; its transitions are obtained by swapping 1 with 4 and 3 with 6. Their final vertices are 1 and 255. Both paths have 47 edges. All vertex pairs were checked natively for inducedness, distinctness and separation. The saved Lean row checks concern these exact concrete vertices.

Among the $48^2=2304$ pairs containing one vertex from each path, the counts at Hamming distances 0 through 8 are

$$0,0,160,390,576,658,388,104,28.$$

No saved forest among the 36 selected in round 195 has this distribution. Since cube isometries preserve distances, this proves inequivalence to those 36 forests. The comparison does not classify all faces of all known Q9 snakes.

## Further searches and next step

A connected circuit model with all eight clique restrictions seeks 50 quotient vertices while omitting at most five of the original 51 seed vertices. It remains UNKNOWN after 90.047 seconds. It provides no improvement to the previous four-omission exclusion.

For the new 96-vertex paired face, the opposite-face model seeks 97 selected vertices in three induced components, joined through the four prescribed ports. This would produce 192 edges. The query remains UNKNOWN after 120.047 seconds. Its failure to finish is not an incompatibility proof. Models, exact inputs and resource records are saved.

Next, use the three endpoint representatives for unrestricted 50-vertex quotient searches, without an untransported seed constraint. A simpler subfamily forbids all matching steps, as in the new pair; there ordinary cube parity balance is valid and $S\cap h(S)=\varnothing$ is required. Keep the unrestricted family separate from this subfamily. If a 50-vertex quotient path is found, its 100-vertex paired face still needs an opposite-face completion. Exhaustively excluding all three unrestricted endpoint cases would rule out this particular symmetry at that size, not a longer Q9 snake in general.

Memory-related startup refusals and interrupted Lean compilation are retained. They are execution limitations, not mathematical conclusions. No other applications were stopped. The proof-batch receipt and completion record identify which proofs actually passed. Research remains active, with the global optimum unresolved.

## Completed verification

All 89 current Lean modules pass, with 126 theorem dependency reports and no admitted statements. This includes the universal three-endpoint transport theorem in the explicit finite quotient, the full concrete pairwise path and separation checks, and the actual triangle noncontainment statement. The exact orbit classification also has the written distance/transitivity proof above. Native search exhaustion and solver timeouts remain separate from these checked statements. The larger finite calculations were split into smaller blocks after the preserved resource failures; the mathematical statements were retained.
