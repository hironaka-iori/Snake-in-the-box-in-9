# Round 203 independent proof review

This report gives written mathematical arguments and one explicit small example. No compiler, solver, census, or numerical search was run. Only this report was created. The coordinating agent's new finite census is outside the independent verification scope of this review.

## 1. Exact whole-snake criterion

Partition the cube coordinates into a base word z and a block word u. Let h be an involutive cube isometry of the block, and let f be any Boolean function on base words. Define

F_f(z,u) = (z,h^(f(z))(u)).

The map is an involution on the entire cube. For a selected set S, write S_z for its selected block words in fibre z. Construct a graph whose vertices are the base fibres containing selected moved block words. Join neighbouring base words z,w exactly when S_z and S_w meet a common two-element h-orbit.

Then F_f preserves adjacency and nonadjacency of every pair of vertices in S if and only if f is constant on every component of this graph.

Proof. In the same fibre, both block words undergo the same cube isometry. Between fibres of base distance at least two, adjacency is impossible before and after the map. Between neighbouring fibres, adjacency is equivalent to equality of their block words. Equal selectors preserve equality. When selectors differ, equality changes exactly for pairs belonging to the same moved h-orbit: either the two words were equal and become distinct, or they were the two different orbit members and become equal. Fixed words and words in different orbits give no changed relation. Thus every graph edge requires equal selectors, and these are all necessary constraints.

This is a criterion on the concrete coordinates and orbit occupancies; it preserves the complete snake and every nonconsecutive nonadjacency. It does not rely on defining admissibility as an unspecified graph isomorphism.

## 2. Invariance and effective selector components

Applying h in a fibre does not change which h-orbits that fibre meets. The constraint graph is therefore invariant under every switch, including switches that would be inadmissible for S. Admissible switches compose by xor on their component selectors.

Fibres containing only fixed block words contribute no effective selector freedom and should not be counted as independent moves. With r effective components there are at most 2^r images. Applying h globally complements every effective selector, so complementary subsets give cube-isometric images. In particular, the unchanged image and all single-component switches cover every selector choice up to cube isometry when r<=3. At r=4, two-component subsets need separate attention.

## 3. When connectedness removes the apparent freedom

If h has no fixed block word and S is connected, every edge of S that changes base coordinates joins equal moved block words in neighbouring fibres. Its fibres are therefore connected by an edge of the constraint graph. The base projection of connected S is connected, so the selector is constant on all occupied fibres. The result on S is either the identity or the ordinary global block isometry h.

The same conclusion holds whenever S contains no h-fixed block word, even if h has fixed words elsewhere. More precisely, along a connected snake, a selector can change only on a base-coordinate edge whose common block word is fixed by h. A fixed selected vertex alone is insufficient to allow this change.

If t is the number of such fixed-word base edges along the snake, the effective component count satisfies r<=t+1. To see this, project the path onto its occupied base fibres and remove those t edges. Removing t edges from a connected graph creates at most t+1 components. Every remaining projected edge is a constraint edge; further constraint edges can only merge components. Discarding components with no moved selected words cannot increase r.

## 4. Classification of involutions with fixed block words

Write h(u)=pi(u) xor b. Involutivity requires pi^2=id and pi(b)=b. Thus pi is a product of disjoint transpositions, and b has equal entries on each transposed pair.

A fixed word exists exactly when b is zero on every coordinate fixed by pi. Necessity follows from the fixed-word equation u xor pi(u)=b. Conversely, on each transposed pair this equation can be solved independently, and its fixed-coordinate equations are zero. Choose a solution t. Conjugation by translation through t replaces b by b xor t xor pi(t)=0. Hence h is conjugate to disjoint coordinate swaps.

With at most three block coordinates, a nonidentity involution with fixed points has only one swap. Any unchanged extra block coordinate can instead be treated as a base coordinate. The original selector is then a special case of a selector allowed to depend on that extra coordinate. After the conjugating translation, this is covered by the two parity choices of round 202.

The first additional fixed-point case is consequently two simultaneous swaps on four coordinates. Although the full map factors algebraically into two controlled single swaps, admissibility of the product does not imply that either factor is admissible on the original snake.

## 5. Explicit simultaneous-swap example

Use Q5, with bit 4 as the base and bits 0,1,2,3 as the block. Set h=(0 1)(2 3) and f(z)=z. Consider the path

S = [5,1,0,16,20,22,23,31,29,25].

Its image is

T = [5,1,0,16,24,25,27,31,30,22].

In the base-zero face, the ordered block path is [5,1,0]. In the base-one face it is [0,4,6,7,15,13,9]. These are induced block paths and their vertex sets intersect only at 0, so the displayed S is induced. The second block path has transition sequence [2,1,0,3,1,2]; its three-step and five-step subintervals have endpoint distance three, and its even subintervals have distinct endpoints, establishing the required nonconsecutive separations.

The h-image of the second face is [0,8,9,11,15,14,6]. It is induced because h is a cube isometry, and its vertex set still intersects {0,1,5} only at 0. Thus T is induced and the whole-snake transformation is admissible.

Applying only the controlled swap (0 1) sends the selected block word 6 to 5, producing an unwanted cross-face edge to the first vertex of S. Applying only (2 3) sends the selected block word 9 to 5 and also produces that chord. Both individual same-selector factors fail on S, while their simultaneous product is valid.

The two paths are not cube-isometric, even after reversal. The unique coordinate used three times in S has successive occurrence gaps 3 and 5; the unique coordinate used three times in T has gaps 3 and 3. Coordinate permutations preserve these gaps and reversal reverses their order.

This example does not prove nonreachability by arbitrary sequences of other round-202 moves. It demonstrates only that simultaneous admissibility cannot be inferred from admissible individual factors, and supplies an explicit change of whole embedding. No record or novelty claim is made.

## 6. Exact endpoint-growth constraints

There is an important distinction between preserving the old snake and preserving a proposed enlarged set. If a candidate vertex v is added to S and the ordinary constancy criterion is imposed on all of S union {v}, every existing contact with v is preserved. Such a condition cannot repair an initially blocked endpoint addition.

For the intended operation, first impose the equality constraints for S. Fix a proposed preimage vertex v outside S and an endpoint t of S. Require F_f(v) to be adjacent to F_f(t) and to no other selected image. This yields necessary and sufficient additional constraints as follows.

For a pair v,s in neighbouring base fibres whose block words belong to a common moved orbit, let r=0 when their block words are equal and r=1 when they are distinct h-partners. Their images are adjacent exactly when

f(z_v) xor f(z_s) = r.

Therefore use this equation for s=t, and use

f(z_v) xor f(z_s) = r xor 1

for every other affected selected vertex. All unaffected pairs have invariant adjacency and must already have the required relation. These include same-base pairs, pairs with base distance at least two, distinct h-orbits, and the fixed-word cases. If an invariant pair has the wrong relation, reject the candidate.

After contracting the equality components for S, all new xor constraints are incident to the component or new variable containing z_v. Thus feasibility is a signed-star consistency condition: parallel requirements must agree and every self-loop must have label zero. Unconstrained selectors can be chosen arbitrarily and extended to the rest of the cube. Since F_f is injective and preserves every old pair relation, satisfying these conditions makes F_f(v) a valid new endpoint of the transformed whole snake.

If v was already a valid endpoint addition and all new labels are chosen to preserve its existing relations, this reduces to constancy on the enlarged set's constraint graph. The labelled version is needed to remove old blockers or create a previously absent endpoint edge.

## 7. Scope of self-symmetry statements

If the selected image equals S and every pair relation is preserved, the restriction to the finite induced path is the identity or reversal. That intrinsic classification is unchanged by using larger blocks. A controlled block map can nevertheless produce a different embedding of the entire snake. Claims about this latter operation should specify the coordinate block, the involution, selector components, and which finite collection of snakes was actually examined.

The coordinating agent's reported census has not been independently repeated here. The statements above establish the mathematical criteria and their limitations, rather than any new numerical closure claim.
