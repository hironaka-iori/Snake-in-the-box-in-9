# Round 204 independent proof review

This report contains written proofs and one explicit example. No computation, census, compiler, solver, or delegated task was run. Only this report was created. Numerical results supplied by the coordinating agent are not independently verified here.

## 1. Exact cyclic criterion

Write a cube vertex as (z,u), with base word z and block word u. Let h be a block cube isometry of finite order m, and let f take values in Z/mZ. Define F_f(z,u)=(z,h^(f(z))(u)). For selected block sets A=S_z and B=S_w in neighbouring base fibres, put d=f(w)-f(z).

Every selected pair retains its adjacency status exactly when, for all u in A and v in B,

[u=h^d(v)] if and only if [u=v].

This is the complete condition. Pairs in one fibre undergo the same block isometry. Pairs with base distance at least two remain nonadjacent. For neighbouring base fibres, adjacency is precisely equality of block words, giving the displayed criterion.

Equivalently, h^d must fix A intersect B pointwise and satisfy

h^d(B minus A) intersect A = empty.

Fixing the shared words protects actual cross edges; the second condition prevents new cross edges and is independently necessary.

For an h-orbit of length ell, a shared word requires d=0 modulo ell. Two distinct selected words u=h^r(v) forbid d=r modulo ell. Different orbits impose no condition. This describes the general cyclic problem using word stabilizers and forbidden residue classes.

## 2. The order-three specialization

Every orbit has size one or three. A common moved selected word forces d=0. A distinct selected pair in one moved orbit forbids exactly one of d=1 or d=2. Fixed words supply no additional restriction.

Equality may also be forced without a common moved word. If one fibre selects one orbit member and the other selects the remaining two, both nonzero differences are forbidden. The same phenomenon can arise from different orbits forbidding opposite differences.

Thus, after collecting all constraints for an edge, its allowed set is one of {0}, {0,1}, {0,2}, or {0,1,2}. Contract every edge with allowed set {0}, including those forced by combined exclusions. The remaining problem is a three-state modular constraint problem. It is not ordinary proper three-colouring: equal phases are always permitted, and a constant global phase is always a solution.

A nonzero phase difference is possible only when every moved orbit meeting both fibres contributes exactly one selected word on each side, those two words are distinct, and all resulting forbidden nonzero differences agree. Richer occupancy in a shared moved orbit forces equality.

## 3. Connectedness and stabilizer rigidity

For order three, if a connected selected snake contains no h-fixed block word, every actual cross-fibre path edge uses a common moved word and forces equal phases. The projected path connects all occupied fibres, so the phase is constant on them. The action on the whole snake is an ordinary global rotation.

More generally, a phase change along an actual cross-fibre path edge must belong to the stabilizer of its common block word. For order three, any nonzero phase change therefore occurs at an h-fixed word. The presence of a fixed word alone does not create freedom: other selected pairs can still force equality across that fibre edge.

For composite order, absence of h-fixed words is insufficient to infer equality of phases. A moved word can have a shorter orbit and be fixed by a nonidentity power of h. The appropriate hypothesis is trivial stabilizer for the selected words, or a connected collection of fibre edges on which the common selected words have trivial pointwise stabilizer.

## 4. Constraints change under admissible rotations

Let D_zw be the allowed relative phases for the original selected set. If F_f is admissible and d_0=f(w)-f(z), the allowed phases for a subsequent rotation satisfy

D'_zw = D_zw - d_0.

Indeed, an additional relative phase d gives the original total phase d_0+d. Since the first map preserved every pair relation, the second map is admissible exactly when this total lies in D_zw.

The forced-equality graph remains invariant under admissible changes: singleton allowed sets remain {0}; nonsingleton sets retain their cardinality. The labels on two-element allowed sets can change. Admissible phase assignments for one fixed selected set therefore need not be closed under addition, and an admissible controlled rotation cannot automatically be repeated.

There is nevertheless a useful reduction for iteration with the same block and the same cyclic action. Any sequence of maps, each admissible on its current whole snake, composes to one controlled phase assignment. Its cumulative assignment is admissible on the original snake. Hence enumerating all admissible assignments from that original snake already covers every finite sequence using this fixed action. This statement does not cover changing the coordinate block or the acting group between steps.

## 5. Small example and the factorization caveat

In Q4 take bit 3 as the base, and let h rotate block coordinates 0 to 1, 1 to 2, and 2 to 0. Use phase zero in base face zero and phase one in base face one. The induced path

S=[5,1,0,8,10,11,15]

maps to

T=[5,1,0,8,12,14,15].

The first-face block path is [5,1,0]; the second is [0,2,3,7]. Both are geodesic, and their vertex sets intersect only at 0. Its rotated second-face path [0,4,6,7] also meets {0,1,5} only at 0. These observations prove the two whole paths are induced.

Applying phase two instead gives second-face block words [0,1,5,7], which create extra cross-face edges at 1 and 5. Thus one admissible phase assignment need not have an admissible square.

The decomposition h=(0 1) composed with (1 2) does not give two individually admissible same-selector maps on S. The first individual swap creates a contact at block word 1, and the other creates one at block word 5. However, swapping (0 2) first is admissible, and the alternative factorization h=(1 2) composed with (0 2) works with the second factor assessed on the changed path. Therefore this example disproves automatic admissibility of a prescribed factorization; it does not disprove the existence of every possible admissible involutive factorization. No general factorization or nonfactorization theorem is established here.

## 6. General finite-group gluing criterion

Let G be any finite group of block cube isometries. Assign g_z in G to each occupied base fibre and map (z,u) to (z,g_z(u)). For neighbouring fibres A=S_z and B=S_w, the exact condition is

g_z^(-1)g_w belongs to K(A,B),

where K(A,B) consists of the elements that fix A intersect B pointwise and send B minus A outside A. This gives explicit local constraints for gluing the block isometries, including preservation of nonedges. K(A,B) contains the identity but need not be a subgroup.

If relative maps are chosen first, they must also be consistent: reverse-oriented edges use inverse maps and the ordered product around every closed base walk is the identity. This is necessary by cancellation. It is sufficient by choosing one root isometry and defining the other fibre isometries by products along base paths. The closed-walk condition makes this independent of path choice.

Common left multiplication of all g_z gives an ordinary global block isometry, so one root map can be normalized to identity when conclusions are taken up to cube isometry. A separate overlap constraint against a fixed external seed must also be transported before using this reduction.

If a connected set of fibre edges has common selected words with trivial pointwise stabilizer in G, every relative map on those edges is the identity, forcing a single global isometry. Trivial stabilizers of individual selected words imply this condition along every actual cross-fibre path edge. Local isometries differing by an element that fixes every selected word in that fibre also have identical action there.

## 7. All-isometry classification for a single coordinate cut

For two faces with selected projected sets A,B, normalize the first face map to identity. Write C=A intersect B. The exact conditions on the relative cube isometry h are

h(c)=c for every c in C, and h(B minus A) intersect A is empty.

If the whole snake uses both faces, connectedness implies C is nonempty. Choose an anchor c in C. Every block cube isometry fixing c has the unique form

h(x)=c xor pi(x xor c),

where pi is a coordinate permutation. It fixes all of C exactly when pi fixes every row x xor c for x in C.

For each coordinate, form its column signature across these rows. The permitted permutations are exactly those that permute coordinates within classes of identical signatures. Necessity follows by inspecting each coordinate of each fixed row; sufficiency follows by reconstructing those rows from their unchanged columns. Therefore the full pointwise stabilizer is a product of symmetric groups, one for each signature class. This includes all relative isometries, with no restriction on their order. The collision-avoidance condition remains necessary after enumeration of the stabilizer.

If all signatures are distinct, the only relative isometry is the identity. For d block coordinates, at least 1+ceil(log2(d)) crossing points are necessary for distinct signatures to be possible, since the anchor row is zero and the other |C|-1 rows provide at most 2^(|C|-1) signatures. In particular, eight block coordinates require at least four crossing points for this sufficient rigidity criterion to be available. Four crossing points do not guarantee distinct signatures, and collision avoidance can force rigidity even when signatures repeat.

If C is empty, the anchor classification does not apply. A connected snake using both faces cannot be in this case; a snake lying in one face has no nontrivial relative action on the absent face.

## Scope

All these maps act on the entire selected snake and preserve its specified path ordering and all pair nonadjacencies. They may produce a different cube embedding. A map preserving the same selected vertex set still restricts to the identity or reversal of the finite path. The statements do not establish new extremal bounds or historical novelty, and no reported finite census is upgraded to a checked proof by this review.
