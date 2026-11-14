# All maximal touching families in the three-cube

Two nonempty subsets of $Q_3$ *touch* if their minimum Hamming distance is at most one. For a shape $S$, write $D(S)=Q_3\setminus N[S]$ for the vertices at distance at least two from every point of $S$. A shape $T$ fails to touch $S$ exactly when $T\subseteq D(S)$.

**Theorem.** On the labelled three-cube there are 4,632 inclusion-maximal families of nonempty pairwise touching shapes. For nonnegative weights on the 255 possible shapes, a maximum-weight family can be found by testing 21 possible choices of its singleton members and making at most 12 independent binary choices for each.

### Geometry of the incompatible shapes

If $S$ is an antipodal pair, $D(S)$ is empty. If its two points are adjacent, $D(S)$ is the parallel edge on the opposite side of the two fixed coordinates. If they are at distance two, $D(S)$ is the other distance-two diagonal in the other parallel square. These facts follow by translating one point to 000 and putting the other at 001, 011 or 111. In the adjacent and distance-two cases, $D(D(S))=S$. Thus among the 28 two-point shapes there are four universal antipodal pairs and **12 disjoint pairs of incompatible two-point shapes**.

Every shape with at least three points touches every two-point shape. Indeed the far set of a two-point shape has size at most two. It follows also that two shapes of size at least three always touch. A singleton can fail to touch a larger shape; this is the only remaining obstruction involving a larger shape.

### Maximal families of one- and two-point shapes

In a maximal family restricted to these sizes, include the four universal antipodal pairs. Select exactly one endpoint of each of the 12 incompatibilities among two-point shapes. At least one must be included: if two compatible singletons respectively blocked the two choices, their far sets would force different non-touching singletons. More explicitly, if $s$ blocks $P$ then $s\in D(P)=P'$, and if $t$ blocks $P'$ then $t\in P$. Since $P,P'$ have all cross-distances at least two, $s,t$ cannot coexist. All the other selected pairs themselves block neither member. At most one choice is allowed by definition.

Given the 12 choices, adjoin all compatible singletons. Those singletons automatically touch one another. To see this, take two nonadjacent distinct vertices, translate the first to 000, and permute the second to 011 or 111. For 000 and 011 the incompatible pair $P=\{000,100\}$ and $P'=\{011,111\}$ has one vertex in each member; the same pair separates 000 and 111. Whichever of these two-point shapes is selected blocks one singleton. Hence every orientation yields a unique maximal small family, giving $2^{12}=4096$ in total.

At most two of its members can be singletons, as the cube has no triangles. A prescribed vertex $s$ belongs to a chosen two-point shape in six of the 12 binary pairs (the seventh pair containing $s$ is antipodal). In each of those six pairs the choice must be the one containing $s$: the other one is disjoint from its closed neighbourhood. The other six choices are unrestricted. Exactly $2^6=64$ orientations admit $s$ as a singleton. For adjacent $s,t$, the two sets of six restrictions have exactly one in common, on the edge $\{s,t\}$; opposite choices would force $s,t$ to be nonadjacent. Thus the adjacent singletons fix 11 choices, leaving precisely two orientations per edge. There are 12 cube edges. Therefore 24 orientations admit two singletons, $8\cdot64-2\cdot24=464$ admit one, and the remaining 3,608 admit none.

### Passing to arbitrary nonempty shapes

Larger shapes do not constrain any two-point shape, so every full maximal family again induces one of the 4,096 orientations. Choose any subset $J$ of the compatible singletons and include exactly these singleton shapes. Adjoin every shape of size at least three touching all members of $J$. This is a maximal family. For a compatible singleton $s$ omitted from $J$, the four-point shape $D(\{s\})$ excludes it. This four-point shape touches every other singleton in $J$: if $s=000$ and a neighbour is $001$, then $011\in D(\{s\})$ is adjacent to that neighbour. There is no way to adjoin the omitted singleton. This construction is exhaustive because every admissible large shape must belong to a maximal family.

The exact count is

$$
3608+2\cdot464+4\cdot24=4632.
$$

### Computing an exact weighted obstruction

Even more directly, first choose the singleton members: the empty set, one of eight vertices, or one of the twelve edges gives 21 cases. Include every allowed large shape and antipodal pair. For each incompatible pair of two-point shapes include the heavier allowed member, if either is allowed. With nonnegative weights nothing is gained by omitting an otherwise available shape. Maximize the sum over the 21 cases. This proves the optimization statement without enumerating the 4,632 families.

For a fixed parity of the chronological intervals of a projected snake, weight a shape by its multiplicity as an interval trace. The maximum calculated above is the **exact clique number** in the graph in which intervals conflict whenever their traces touch. Repeated intervals of identical type all conflict and can all be included. This gives the strongest possible pigeonhole obstruction based solely on a single same-parity clique of retained traces. The argument works with disconnected shapes as well as the connected traces occurring here.

[Independent Python implementation](touching_families.py) and [bank census](bank_exact_cliques.cpp).

## Consequence for 192-edge constructions

For the 131 saved nine-cube snakes, 84 retained triples and 192 possible repeated positions, the exact clique criterion excludes **24,150 of 2,112,768 indexed choices**, including all 7,713 excluded by the original five shapes. Every seed has exclusions, ranging from 38 to 512. Entry 1 at position 95, retaining bits 0, 1 and 5, has a family of **42** pairwise conflicting intervals of one parity. Its demand exceeds capacity by ten.

The native scan computes the maximum using the 21 cases above. A separately written program reconstructed all 24,150 positive cases, exhibited actual interval cliques, checked every distinct trace-type pair, and checked one maximizing position for each of 11,004 seed/triple rows. [Results](bank-exact-summary.json), [case list](bank-exact-cliques.csv), [independent checks](verify_exact_cliques.py). Lean checks the generic step of selecting heavier endpoints of mutually independent incompatible pairs in [Matching.lean](Matching.lean); the cube classification and its enumeration are the written proof above.
