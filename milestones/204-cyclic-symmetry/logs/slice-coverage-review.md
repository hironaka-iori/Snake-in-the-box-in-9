# Round 204 slice-isometry coverage review

Source review only: face_isometries.py, slice_census.py, and slice_image_census.py were read. None was executed. This report does not independently verify the reported completion records or numerical class counts. No mathematical or implementation flaw making the stated image enumeration incomplete was found.

## 1. Family and normalization

Fix a coordinate partition into base and block coordinates. Write S_z for the selected block words in occupied slice z. The family assigns an arbitrary cube isometry g_z of the entire block cube to each occupied slice, keeping the base word fixed. Only assignments preserving every selected pair's adjacency and nonadjacency are admissible.

Postcomposing all g_z with the inverse of one occupied root map is an ordinary global cube isometry on the block coordinates. It preserves admissibility and the cube-isometry class of the whole image, and makes the root map the identity. Thus root normalization loses no image class. Maps on unoccupied slices can be extended arbitrarily and impose no selected-pair restrictions.

## 2. Exact relative-map list

For neighbouring occupied slices with original selected sets A and B and nonempty C=A intersect B, the relative map r=g_A^(-1)g_B must fix C pointwise and satisfy r(B minus A) intersect A empty. This is exactly the criterion for preserving every pair between these slices.

Choosing anchor c in C, every cube isometry fixing c has the form r(x)=c xor pi(x xor c). Fixing every word in C is equivalent to permuting coordinates only within classes whose column signatures across C xor c are identical. The relative() implementation enumerates every such permutation, constructs the complete isometry table, and filters exactly the forbidden new contacts. Therefore its list is complete.

Taking inverse tables supplies the exact reverse-direction list. If r fixes C and r(B minus A) avoids A, then r^(-1) fixes C and r^(-1)(A minus B) avoids B; the converse follows by inversion.

The single-face implementation uses the same enumeration in unpacked coordinate positions. The absent cut coordinate is consistently excluded from the anchor and permutation.

## 3. Frontier selection is complete

The graph of occupied base fibres with an edge for each nonempty original crossing intersection is connected. Projecting the original connected snake gives a walk through every occupied fibre, and each step changing base coordinates supplies precisely such an edge.

Consequently, until all slices have been assigned, there is an unassigned slice with an assigned crossing neighbour. Choosing one such neighbour only determines a parameterization of the next map. For every compatible desired next map b and assigned neighbour map a, the relative map a^(-1)b is in the complete precomputed list, so the loop generates b. Choosing the neighbour with the smallest list does not restrict coverage.

## 4. All remaining contacts are checked

The compatible() function examines every already assigned adjacent base fibre, including those with empty original intersection. It requires equal images of each original common word, then requires the total image-set intersection to have exactly the original common-set cardinality.

Because the slice maps are injective, the first requirement already supplies that many distinct common image words. The cardinality equality therefore excludes every additional contact. Together these conditions preserve each labelled cross edge and every cross nonedge. When the original intersection is empty, they correctly require disjoint image sets.

Pairs in one slice are handled by its cube isometry, and pairs in slices of base distance at least two remain nonadjacent. All relevant pairs are therefore covered. The independent full-path assertion at each leaf is additional confirmation, rather than a substitute for this coverage argument.

## 5. Pointwise-image deduplication is safe

Suppose two candidate full isometries a and a' agree pointwise on the selected words A of a slice. Their compatibility with every already assigned slice is identical, since the checks use only these selected images. Thus inserting a signature into seen before the compatibility check is safe.

For completeness of later assignments, take any valid full completion using a. Replace only that slice map by a'. Every selected image is unchanged, so the completion remains valid. If a future slice with selected words B has desired map b and is generated through this neighbour, the required relative map is r=(a')^(-1)b. For every c in A intersect B, validity gives b(c)=a'(c), hence r(c)=c. If some v in B minus A satisfied r(v) in A, then b(v) would equal a'(u) for a selected u in A, contradicting the absence of a new contact. Thus r belongs to the full relative list, and a' composed with r generates b exactly.

This proves that every discarded ambient extension has a completion with the retained representative and the same selected image. Repeating the argument inductively proves image completeness of the deduplicated search. It is essential that the signature records images in the fixed order sorted(S_z), so that equality is pointwise. Equality of unordered image sets alone would not justify the same argument.

The leaf counter in slice_image_census.py is consequently a count after normalization and this pointwise identification. It should not be described as the number of all ambient isometry assignments, or as the number of cube-isometry classes. The separate canonical-class set supplies the latter count.

## 6. Canonical cube-isometry invariant

For a valid ordered cube path, its transition sequence records the unique changed coordinate at every step. Translation changes none of these labels; coordinate permutation relabels them. Renaming labels by first occurrence is a complete invariant under coordinate permutations: equal normalized sequences determine a bijection of used coordinates, which extends to a permutation of all eight coordinates, and a translation then aligns the starting vertices.

For an induced path regarded as an unlabelled vertex set, its only possible orders are the two orientations. Taking the minimum over the forward and reversed normalized transition sequences is therefore a complete cube-isometry invariant in the fixed ambient cube Q8. It does not compare paths in differing ambient dimensions. The scripts' leaf valid() assertions ensure that extracting a direction by bit_length is applied to genuine one-coordinate steps.

## 7. Completion and partition coverage

The DFS checks its limits before exploring each node. A limit raises TimeoutError, marks the current partition and overall result LIMIT, and stops later partitions. Previous completed records remain COMPLETE. A COMPLETE result is therefore not emitted after an interrupted DFS. Relative-list preparation can exceed the nominal wall limit before the next DFS check, which is a timing limitation rather than a completeness error.

For the claimed aggregate result, the records must cover all base subsets of sizes one through seven with the same input source. The required counts are 8,28,56,70,56,28,8, respectively, totaling 254 partitions. Base size zero permits only a global cube isometry, and base size eight has an empty block and acts identically; both cases are trivial. The code's combinations loops cover the required subsets exactly once when each corresponding run completes.

The source review establishes the algorithmic coverage. The separate completion records, matching source hashes and reported absence of new canonical classes still supply the finite empirical premises; those records were not re-executed or independently recounted in this audit.

## 8. Exact scope and iteration consequence

If every reported partition is complete and every image is cube-isometric to the saved 98-edge Q8 snake, the result establishes rigidity of this particular snake under all admissible independent block-cube isometries on slices of every coordinate partition.

This move family is equivariant under global cube isometries: coordinate permutations transport the partition, base translations relabel slices, and block isometries conjugate or postcompose the local maps. Therefore the same one-class result, if its finite premises hold, also implies closure under any finite sequence of these moves, even when the partition changes between steps. Inductively, each current snake is a cube image of the original and the next move transports back to a covered move on that original.

This does not prove that every 98-edge Q8 snake is isometric to the saved one. It does not cover a map that reorders the path by changing its pair relations, changes its length, moves base coordinates conditionally within one step, or uses selected-slice embeddings that do not extend to cube isometries. It supplies no global Q9 upper bound or impossibility proof for 196 edges. Nontrivial ambient local maps may still exist; the conclusion concerns their selected images up to cube isometry.
