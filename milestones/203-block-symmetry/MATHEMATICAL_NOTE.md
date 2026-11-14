# Whole-snake transformations by involutive coordinate blocks

Round 203 extends the controlled square reflection to an arbitrary involutive cube isometry on a coordinate block. The result supplies an exact preservation criterion for the whole snake. It produces a different 50-edge Q7 parent and proves a limitation of this entire transformation family on the saved 98-edge Q8 parent. No longer Q9 snake or new global numerical bound is obtained. No historical novelty claim is made.

## Exact criterion

Write each vertex as $(z,u)$ using a partition of the coordinates. Let $h$ be a cube isometry on the block coordinates with $h^2=\mathrm{id}$, and let $f$ be a Boolean function of the remaining coordinates. Define

$$F_f(z,u)=(z,h^{f(z)}(u)).$$

This is one involution defined on every cube vertex. For a selected set $S$, let $S_z$ be the block words selected above $z$. Form a graph on the base fibres containing a selected word moved by $h$. Join neighbouring base words $z,w$ when $S_z$ and $S_w$ meet the same two-element orbit of $h$.

**Theorem.** The map preserves adjacency and nonadjacency of every pair in $S$ exactly when $f$ is constant on every component of this graph. In particular it takes an entire ordered induced snake to another of the same length.

**Proof.** In one base fibre both words undergo the same block isometry. Base words at distance at least two cannot yield adjacent cube vertices. Between neighbouring base fibres, adjacency is exactly equality of block words. Different selectors change equality precisely when the two block words lie in the same moved two-cycle. Equal selectors preserve it. Fixed words and distinct orbits cannot change equality. Thus each graph edge requires equal selectors and there are no other restrictions. Constancy on edges is equivalent to constancy on components. Involutivity guarantees distinct images of distinct vertices.

Block orbit occupancy does not change under the operation, so the constraint graph is invariant. Composition is xor of the selectors. Complementing every effective selector composes with the global isometry $h$. With two components, identity and one component switch consequently cover all images up to cube isometry.

This is a symmetry between embedded whole snakes, and need not preserve the entire cube graph. If the image is required to equal the original selected set, its restriction to the finite path is identity or reversal: the image of an endpoint determines all successive vertices. No additional intrinsic path automorphism is asserted.

## Rigidity and classification

**Rigidity theorem.** If no selected block word is fixed by $h$, every admissible transformation of a connected snake agrees on it with identity or the global block isometry.

Along a snake edge inside one fibre the selector is unchanged. An edge between fibres has equal block words; these are moved by hypothesis, so the constraint graph forces equal selectors. Induction along the entire snake makes all selected selectors equal. The conclusion also applies whenever $h$ has no fixed word anywhere.

Write a block isometry as $h(u)=\pi u\oplus b$. Involutivity gives $\pi^2=\mathrm{id}$ and $\pi b=b$. A fixed word exists exactly when $b$ vanishes on coordinates fixed by $\pi$. On a transposed pair the two entries of $b$ agree. Choosing a fixed word $c$ gives

$$h(u)=c\oplus\pi(u\oplus c).$$

Thus every involution with fixed words consists of disjoint coordinate swaps, possibly complemented on both bits of individual pairs. Pointwise fixed block coordinates may be moved into the base; allowing the selector to depend on them includes every original selector. One transposed pair is exactly the round202 family. Two simultaneous pairs are the first additional case. Factoring such a map into individual controlled swaps does not imply that the intermediate image remains a snake.

For the specific saved 98-edge Q8 parent, all 56 one-pair graphs, all 840 two-pair graphs and all 3360 three-pair graphs are connected. Four pairs leave no base coordinates. Fixed-point-free cases are covered by the rigidity theorem. This exhausts every involutive coordinate-block isometry, including blocks with pointwise fixed coordinates. Therefore every admissible map of this type produces only a cube-isometric copy of this parent.

The family is equivariant under cube isometries: coordinate permutations transport the partition and translation conjugates each block involution, while relabelling the selector's base. Consequently arbitrary iterations also stay in this parent's cube-isometry class. This conclusion concerns the saved parent, with generic Lean proofs, written classification/equivariance arguments and finite native census premises. It is neither a complete Lean replay nor a classification of all 98-edge snakes.

## A different Q7 parent

Take complemented swaps on coordinate pairs $(0,4)$ and $(1,2)$, simultaneously. Use base coordinates $3,5,6$, and apply the swaps only at base word encoded by 40. The constraint graph has components $\{40\}$ and $\{0,8,32,64,72,96,104\}$.

The saved 50-edge path is

```
0,1,3,7,6,14,12,13,29,25,27,26,18,50,51,49,53,37,36,100,68,69,85,81,80,88,72,73,75,79,95,94,86,118,119,103,99,98,106,122,123,121,125,124,60,56,40,41,43,47,63
```

Its image is

```
0,1,3,7,6,14,12,13,29,25,27,26,18,50,51,49,53,37,36,100,68,69,85,81,80,88,72,73,75,79,95,94,86,118,119,103,99,98,106,122,123,121,125,124,60,62,63,47,43,41,40
```

The endpoint Hamming distance changes from 6 to 2, proving that the two snakes are not cube-isometric even allowing reversal. Lean checks all 51-by-51 pair relations of both paths, all vertices' bounds, the positionwise transformation, and both endpoint distances. This is a different representative at the same 50-edge length. The saved original is rigid under round202 moves; equivariance shows arbitrary iterations of those moves cannot reach this new cube class.

All 645120 relative cube isometries were enumerated for original/new and new/new parent pairs. Each pair has minimum projected overlap 2 and maximum 92 separated vertices after independently trimming to one contiguous interval in each parent. The ten-omission cutoff is exhaustive for that maximum: any result with at least 92 vertices deletes at most 10 of the original 102, hence has at most 10 projected collisions. Enumerating all 66 first-parent intervals with at most 10 omissions and the longest surviving interval in the other parent covers every such possibility. Witnesses attaining 92 are saved. Thus the new shape gives no improvement in this restricted joining family.

## Finite scope and remaining direction

The two-pair census covers 180, 420 and 840 choices for the saved Q6, Q7 and Q8 parents. Only the stated Q7 choice has more than one component. For the 131 saved Q9 snakes it covers 198072 choices; the 74 nontrivial component switches all stay in existing bank classes. All these graphs have at most two components, so complements cover every selector combination. Together with round202 and equivariance, this proves closure of those bank classes under arbitrary iterations using one or two pairs, conditional only on the recorded native census correctness. Three- and four-pair Q9 maps have not been enumerated. The new Q7 parent's complete one-/two-pair orbit has not been enumerated either.

Three-pair graphs were enumerated for both Q7 parents (840 each) and the Q8 parent (3360); all are connected. No solver searches were run in this round.

For a proposed extension, preserve the old snake $S$ first. Choose a preimage vertex $v\notin S$ and an endpoint $t$. For an affected pair $v,s$ across neighbouring base fibres, put $r=0$ when their block words agree and $r=1$ when they are the two orbit partners. Their images are adjacent exactly when

$$f(z_v)\oplus f(z_s)=r.$$

Impose that equation for $s=t$, and its opposite label $r\oplus1$ for every other affected selected vertex. Unaffected pairs must already have the required adjacency status. After contracting the old equality components, these equations all meet the variable containing $z_v$. They are feasible exactly when repeated requirements agree and every self-loop has label zero. Injectivity then makes the image vertex a valid new endpoint. Requiring ordinary pair preservation on $S\cup\{v\}$ instead would preserve any old blockers, so would not express this intended repair. Lean checks the displayed matching law; the full geometric extension interpretation and feasibility argument are written. No endpoint-growth search is claimed.

For the saved Q8 parent, changing from involutions to higher-order block isometries is now a justified next proof direction: merely increasing the size of an involutive block has been exhausted. A group-valued selector would require new cross-fibre compatibility constraints and an example changing the whole embedding. There is no established prediction that it yields a longer snake. The earlier necessary index3/95 condition on the saturated overlap-five construction remains a separate unresolved route.

## Verification record

There are 56 accepted Lean modules and 71 theorem dependency reports: 16 general reports, 3 concrete data reports, 51 single-row proofs and 1 aggregate theorem. Only standard Lean logical axioms occur. The generic results cover arbitrary Cartesian product graphs under explicit involution and block-isometry hypotheses. Component language, classification, cube-isometry invariance, closure deductions and full geometric growth assembly have the written scope specified above. Native censuses are not Lean proofs.

The monolithic concrete proof and an eight-row split exceeded the 256MiB private-memory gate. Splitting the same complete statement into one-row modules succeeded. The aggregate initially failed because a decision procedure encountered a locally generated proof term; a direct arithmetic proof repaired that elaboration issue. Failed sources, execution plans and logs are preserved. Accepted proof sources and objects are pinned in their receipts. No weakened pair statement or unproved placeholder was accepted.

The independent review supplies written proofs and a separate small example; it did not rerun the censuses. Both existing manuscripts are updated in place and mirrored under paper/. The independent rebuild of archived upper bound 235 remains pending, and bounds 233/234 remain conditional.
