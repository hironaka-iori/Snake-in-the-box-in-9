# Round 205: certificate architecture for arbitrary slice isometries

This is a written mathematical and design review. No enumeration, solver, compiler, or certificate checker was run for this review. The native round 204 results are inputs to certificate generation, not premises accepted as proved. The intended conclusion concerns the particular saved 98-edge path in Q8 and all 254 nontrivial coordinate partitions. It gives no classification of all 98-edge paths and no upper bound in Q9.

## Recommendation

Use the prepared fixed-tree finite constraint model, with a separately proved geometric completeness bridge. Its arc-elimination and residual-cover proofs can be reused directly. A contextual cover of **selected images** remains a sound alternative where materializing an absolute domain is expensive. Both approaches should use explicit cube-isometry representatives, exact relative-map completeness, witnessed rejections, and explicit global cube-isometry witnesses at complete assignments.

During this review, the implementation reported prepared domains for all 254 partitions: 5,821 variables, 23,892 initial values, 16,166 arc eliminations, and 460,858 compatibility entries, with residual domain size at most four. These figures were supplied by the main investigation and were not independently recomputed here. Given those prepared domains, switching back to a contextual tree solely for architectural preference is unnecessary. The completed finite-model coverage proofs must remain distinguished from geometric domain completeness, compatibility-table interpretation, and global leaf-isometry proofs.

Two mathematical reductions discharge every partition with one block coordinate, and discharge the two-block-coordinate partitions once the round 202 active-graph connectedness facts are kernel-checked. They remove 36 of the 254 partitions from the assignment-tree problem. The remaining 218 partitions still need complete certificates or other proved reductions. This count does not predict the fraction of verification work saved.

The essential invariant should be that an arbitrary admissible completion agrees with a node **on each selected word**. Equality of its unused local-map values is unnecessary. This makes the existing pointwise-image deduplication a direct consequence of the completeness theorem.

## 1. Exact theorem to certify

Let the source path be the fixed list p_0,...,p_98 in Q8. For a nonempty proper set of base coordinates, write a vertex as (z,u), and let S_z be its selected block words. An admissible assignment chooses a cube isometry g_z on the block for each occupied slice and preserves adjacency and nonadjacency for every pair of selected vertices under (z,u) -> (z,g_z(u)).

The desired conclusion is that every admissible image of this source list is obtained by a global Q8 cube isometry, with either the original or reversed path orientation. Empty slices have no selected effect and require no search variables.

For adjacent occupied slices z,w, admissibility is equivalent to

    g_z(u) = g_w(v) if and only if u = v,
    for every u in S_z and v in S_w.

Within a slice, an isometry preserves every distance. Nonadjacent base slices cannot contain adjacent full vertices. These facts prove that the displayed finite conditions are sufficient as well as necessary for whole-selected-set pair preservation. They must be part of the generic cube bridge, rather than assumed from the Python checker.

The original path makes the graph of occupied slices joined by actual crossing edges connected: project the consecutive source vertices onto the base coordinates. Every changed base coordinate gives adjacent slices with a common block word. Thus a search can always choose an unassigned slice with an assigned actual-crossing neighbour.

## 2. Kernel-checkable contextual cover and the shared completeness invariant

At a node store an assigned set of slices and one explicit block isometry for each assigned slice. Its selected values are the node state. Normalize one occupied root map to the identity by common left composition; this common composition is a global cube isometry.

Choose an unassigned slice z and an assigned actual-crossing neighbour w. Put A = S_w, B = S_z, C = A intersection B, and choose c in C. If a complete admissible assignment extends the node on selected words, its desired map b at z satisfies

    r = g_w inverse composed with b,
    r(c') = c' for c' in C,
    r(B minus A) intersection A = empty.

This remains true when the completion uses a different ambient extension at w, because that extension agrees with g_w on A. Consequently the relevant relative domain can be defined solely from A and B, independently of the current completion.

Every cube isometry fixing C pointwise has the form

    r(x) = c xor pi(x xor c),

where pi permutes coordinates within equal column-signature cells of the words c' xor c for c' in C. Prove this classification once. A generic complete permutation enumerator then gives a complete finite domain. Apply the extra-contact condition as an exact filter, or supply a conflicting pair for each filtered-out permutation. A native list and its reported length do not establish domain completeness.

For each domain element form g_z = g_w composed with r. Its certificate entry must have one of these outcomes:

1. **Rejection:** two explicitly identified selected vertices in adjacent assigned slices violate the equality condition in Section 1.
2. **Duplicate:** an earlier candidate has exactly the same pointwise values on the selected words of S_z. Its child covers this candidate.
3. **Child:** a recursively certified node adding z.

The verifier must cover every relative-domain element. It need not reproduce the native variable-order heuristic, time counters, node counters, or `COMPLETE` flag. A frontier choice only needs an unassigned z, an assigned actual-crossing neighbour w, and nonempty C. Compatibility with every assigned adjacent slice is needed, including adjacent pairs with empty original intersection.

The proof is induction on the number of unassigned occupied slices. Take an arbitrary admissible completion. Relative-domain completeness supplies its candidate. A witnessed rejection is impossible for that completion. Pointwise duplicates preserve the extension invariant. The corresponding child therefore applies. The leaf witness then proves the conclusion. This induction also explains why inserting a pointwise duplicate into `seen` before compatibility is sound: candidates with the same selected values have identical compatibility outcomes.

Do not deduplicate by an unordered image set. The labelled equality at original crossing words, and the indexed final path image, use the pointwise image function.

## 3. Leaf witnesses and shared subproofs

Each leaf should carry an orientation bit and an explicit permutation of the eight coordinates. Its translation is determined by the first source and image vertices in that orientation. Check the 98 corresponding transition directions, or the 99 corresponding vertex images. A generic telescoping argument turns the transition check into equality of the full lists.

This avoids making the Python canonicalization routine part of the trusted proof. It also avoids enumerating all global cube isometries at a leaf. Allow the full Q8 coordinate permutation and reversal. The native result alone does not justify restricting leaves to forward, partition-preserving global maps.

Relative domains are shared per oriented actual-crossing pair within a partition. Pointwise candidate evaluations and verified subtrees can also be shared. A directed acyclic certificate graph is sound if node states are checked exactly and every dependency has smaller remaining depth; hash equality alone is insufficient. Such sharing is optional and has no claimed reduction until measured.

A further valid pruning rule uses a global block isometry that fixes every previously assigned selected image pointwise and maps one candidate's selected images to another's. Common left composition transports every admissible completion between the two candidates, while preserving the desired global-isometry conclusion. Require an explicit isometry witness and verified actions. This is more work to implement than ordinary pointwise deduplication and should be added only where it substantially reduces the certificate.

## 4. A universal reduction for blocks of size one and two

### One block coordinate

An isometry of Q1 fixing one word is the identity. Across every actual crossing, the relative local map fixes the common word, so the two local maps coincide. The connected crossing graph forces all local maps to be equal. Every admissible assignment is a single global block isometry. This handles all eight base-size-seven partitions without any source-specific assignment census.

### Two block coordinates

Let tau_0 exchange 00 with 11 and fix 01 and 10. Let tau_1 exchange 01 with 10 and fix 00 and 11. Both are Q2 isometries. They commute and generate the four-element group

    K = {identity, tau_0, tau_1, tau_0 composed with tau_1}.

An isometry of Q2 fixing a word is either the identity or the reflection in the diagonal through that word, hence belongs to K. Normalize the root local map to the identity. Every actual-crossing relative map belongs to K; connectedness of the crossing graph then puts every normalized local map in K. Write it uniquely as

    g_z = tau_0 raised to a(z), composed with tau_1 raised to b(z),

where a(z), b(z) are binary values.

For epsilon in {0,1}, let B_epsilon consist of those base words whose slice contains a selected block word of parity epsilon. Give B_epsilon the base-cube adjacency relation. Across neighbouring base slices, equality is possible only between block words of equal parity. For the two even words, differing values of a toggle equality for every selected even-even pair. The odd action has the identical property with b. Opposite-parity pairs remain unequal under every map in K. It follows that the full assignment is admissible exactly when a is constant on each connected component of B_0 and b is constant on each connected component of B_1.

In particular, the two parity actions are independent, and every admissible Q2 slice assignment factors into two individually admissible controlled diagonal switches. If each nonempty B_epsilon is connected, the assignment agrees on all selected words with a single element of K. Undoing root normalization proves that the whole image is a global cube-isometric copy.

The native round 202 report says these active graphs are connected for the saved Q8 path. That assertion needs its own finite certificate. For each of 28 coordinate pairs and each parity, a spanning tree on the computed active vertex set is enough: verify the covered set, a root, and an earlier adjacent active parent for every other vertex. Empty active sets need no phase restriction. This discharges all 28 base-size-six partitions without enumerating their arbitrary local-isometry assignments.

This reduction uses connectedness of the selected source and of the two active graphs. Connectedness of the whole source alone does not assert connectedness of each active graph.

### A further elementary restriction in every block dimension

An affine cube isometry x -> pi(x) xor b changes parity by the parity of b. Local maps agreeing at an actual crossing word must have the same parity offset. Therefore a connected selected source has one common offset, and every root-normalized local map has even translation parity. This is a valid generic domain restriction. It does not by itself imply that the local maps are equal.

## 5. What must be proved, and what can be reduced finitely

The reusable mathematical layer needs:

- the representation and classification of cube isometries as coordinate permutations followed by xor translations;
- pack/unpack bijectivity and the decomposition of full-cube adjacency across a coordinate partition;
- the exact selected-image compatibility criterion and connected crossing graph;
- root normalization and completeness of the anchor/column relative domain;
- the selected-image tree-cover induction, including duplicate coverage;
- correctness of explicit global leaf witnesses;
- the one- and two-coordinate reductions above, if used.

If the theorem quantifies arbitrary cube graph automorphisms, the affine-coordinate classification is unavoidable. One proof normalizes the image of zero, identifies the induced permutation of its unit neighbours, and recovers every bit from distances to zero and those unit neighbours. Graph automorphisms preserve graph distance, which is Hamming distance. Alternatively, a theorem may initially quantify a structure explicitly defined by permutation and xor data, provided that narrower statement is stated honestly until the classification bridge is supplied.

Finite kernel reduction can independently establish:

- the exact saved vertex list and its length and induced-path property, reusing an existing checked source certificate if available;
- partition coverage by all nonempty proper eight-bit coordinate masks, with no missing case;
- the computed fibre sets, common-word signatures, and relevant finite domains;
- every rejection pair, duplicate equality, child reference, and leaf witness;
- the active-graph spanning-tree certificates used for block size two.

Source identity must be tied to the same explicit Lean vertex-list constant throughout. A hash can help file handling, but it is not a substitute for proving claims about that list. Native status strings, solver conclusions, and trusted external reductions cannot discharge the finite proof obligations. Use kernel-reduced certificate verification with a proved soundness theorem; do not replace it by `native_decide` or unchecked axioms.

There is no need to prove the source is an optimal Q8 snake to establish this rigidity theorem. Its inducedness, connectedness, stated length, and exact identity are sufficient. If optimization or maximality is mentioned elsewhere, those remain separate assertions.

## 6. Completing the prepared fixed-tree constraint model

A naive absolute domain contains every signed coordinate permutation. The prepared fixed-tree construction can avoid this by using the same complete relative domains as the contextual search. Its geometric completeness follows by induction on a rooted spanning tree of actual crossings.

Put the identity in the root domain. For a tree edge w -> z, compose every parent-domain representative with every relative map fixing S_w intersection S_z and creating no extra parent contact, then retain one representative for each pointwise selected-image signature. For any admissible normalized assignment, the induction hypothesis supplies a parent representative agreeing with its actual parent map on S_w. The relative-map argument in Section 2 then supplies the actual child map before deduplication, and the retained representative agrees with it on S_z. Thus every admissible assignment has a corresponding assignment of domain values. This proves completeness of fixed-tree domains even when full ambient extensions are deduplicated. The retained signatures must be pointwise, and every generated signature must be covered.

Conversely, each domain representative is a cube isometry. For every adjacent occupied pair of base slices, a compatibility-table entry must equal the selected-pair equality criterion of Section 1. Include adjacent pairs with empty common set. Nonadjacent base pairs require no constraint. Once this interpretation is checked, every compatible finite assignment describes an admissible geometric image.

This yields two separate bridges: every admissible geometric assignment reaches the finite model, and every finite assignment has the stated geometric interpretation. The former is essential for exclusion and rigidity; the latter supports leaf verification and rules out an incorrectly interpreted finite model. They should be explicit theorems rather than comments attached to the enumeration.

An arc-consistency certificate is valid if each removed value has no surviving compatible support in a specified neighbouring domain, and the removals have a well-founded order. For a `List.all` blocker certificate, the quantified list must be the entire neighbour domain at that step; checking an arbitrary subset would be unsound. A verified domain erase then preserves every complete compatible assignment. Bitset rows must be proved to encode exactly the intended domain indices and compatibility relation, including the direction of each binary constraint. Out-of-range bits must not silently create or remove allowed values.

Surviving domains do not automatically show a common global isometry: individually supported local values need not be simultaneously compatible around cycles. The residual cover must enumerate every remaining value at each chosen variable, reject branches only with an actual violated constraint, and attach a geometric global-isometry witness to every complete surviving assignment. No Helly property or local-to-global extension principle should be assumed. A proof of finite-model coverage without these witnesses proves coverage only; it does not establish the advertised cube-class conclusion.

A compact rigidity certificate based only on propagation may exist for particular partitions. It can replace a subtree once its soundness is proved and its finite premises checked. It should be an additional certificate format rather than a reason to change the scope of the target theorem.

## 7. Suggested implementation order and final scope

Keep the current finite-model elimination and residual-cover work. In parallel with writing those proofs, establish the generic cube bridge and fixed-tree selected-image completeness theorem, and prepare explicit global witnesses for its leaves. Certify the active graphs and use the one- and two-coordinate reductions where they shorten the final theorem. They can also provide an independent check on those finite-model cases. Split finite checking into manageable independently proved units, and audit the final partition dispatcher for coverage of all 254 masks. No numerical output in this review establishes that any of these Lean obligations has passed.

After those obligations pass, the theorem states that arbitrary admissible slice-isometry assignments on this saved Q8 path yield only its original cube-isometry class. A separate generic equivariance lemma then permits arbitrary repetitions with changing coordinate partitions: conjugating a partitioned transformation by a global cube isometry gives another transformation in the all-partition family. Thus every finite iteration also stays in that class. The native census alone does not discharge this Lean theorem, and this review does not claim that any round 205 certificate has yet been checked.
