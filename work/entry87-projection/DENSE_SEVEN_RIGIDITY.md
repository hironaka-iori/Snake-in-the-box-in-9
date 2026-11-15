# Dense seven-cube forests and a test for the global nine-cube bound

An induced linear forest is a vertex set whose induced graph is a disjoint union of paths, including isolated vertices. A seven-cube contains at most 64 vertices of such a forest, by partitioning into four-cubes. Call a 64-vertex forest half-full.

**Every seven-cube linear forest on 62 or 63 vertices extends to a unique half-full forest.** The threshold is sharp. Exactly 5,134,080 of the 61-vertex forests are maximal under inclusion. No vertex can be appended to any of those forests while preserving the linear-forest condition.

| Vertices | Labelled forests | Contained in a half-full forest | Outside every half-full forest |
|---|---:|---:|---:|
| 64 | 9,424 | 9,424 | 0 |
| 63 | 603,136 | 603,136 | 0 |
| 62 | 18,998,784 | 18,998,784 | 0 |
| 61 | 397,775,616 | 392,641,536 | 5,134,080 |
| 60 | 6,405,713,664 | 5,987,783,424 | 417,930,240 |
| 59 | 87,364,326,784 | 71,853,401,088 | 15,510,925,696 |

### Why each extension is unique

The 9,424 half-full forests have six shapes up to cube isometry. Relative to any one of them, the nearest different half-full forest removes at least eight vertices and adds at least eight. This follows by generating the full isometry orbit from each representative and comparing those six representatives to all 9,424 labelled masks. Thus two half-full forests intersect on at most 56 vertices. Every subset with 57 or more vertices is in at most one half-full forest. For population n between 57 and 64 the exact number contained in a half-full forest is therefore 9,424 times the binomial coefficient C(64,n).

We independently count all forests by joining opposite six-faces and testing the induced degrees and acyclicity. The denser of the two six-faces may be fixed up to cube isometry. To place the other side it suffices to retain one representative per orbit of the symmetry group fixing the first face. Its orbit size restores the number of labelled placements. The streaming enumeration constructs the opposite six-face from two five-faces. For 62 through 64 vertices the population and component histograms also agree with direct joins of the complete labelled six-face inputs. At 62 and 63 the subset count accounts for every forest. At 61 any possible extension to 62 would also extend to 64, proving maximality for every remaining 61-vertex forest. The verifier supplies a concrete maximal set and tests all other sites. [Enumerator](near_full_faces.cpp), [marked counts](stream-marked-seven-census.txt), [classification and orbit construction](seven_deletions.py), [distance and counting verifier](dense_rigidity.py), [exact results and maximal witness](dense-seven-rigidity.json).

### How this can improve the global bound

Suppose a nine-cube snake has 233 edges. The nine coordinate-use counts sum to 233, so some coordinate changes at most 25 times. Its two faces contain alternating runs of the path, and each has at most 13 components. At least one face contains at least 117 of the 234 vertices. Shortening its components at their ends gives an **eight-cube induced linear forest on exactly 117 vertices with at most 13 components**. Ruling out this single extremal configuration would prove that every nine-cube snake has at most 232 edges, since a longer snake has a 233-edge prefix.

Splitting such a 117-vertex forest along any coordinate leaves one seven-face with at least 59 vertices. For 62, 63, or 64 vertices the dense-face classification gives precisely 192, 18, or 6 shapes, respectively. To test a fixed shape, choose the opposite vertices freely, require maximum degree two, and require at least 104 induced edges, since a forest on 117 vertices and at most 13 components has at least 104 edges. Every cyclic component found is excluded explicitly. [Facet decision](dense_eight.py).

There is a further bound that uses no solver. A singleton in a seven-face can have at most one crossing. A two-vertex component can also have at most one crossing, since both crossings together would make a square. Consequently each such short face component contains a global endpoint of its path, counting an isolated global vertex twice. If one face contains t singleton or two-vertex components, the full forest has at least ceil(t/2) components. In particular, a face consisting of 32 disjoint edges forces at least 16 components. Even if up to eleven of its vertices are deleted, at least 27 short components remain. This excludes all these subsets in the 117-vertex test. The full global extremal configuration remains unresolved.

### Every coordinate of the 117-vertex test must be nearly balanced

**All 216 shapes on 62, 63 or 64 vertices have now been excluded as a face of a 117-vertex eight-cube forest with at most 13 components.** Hence each of its eight coordinate cuts must divide the forest into 56+61, 57+60 or 58+59 vertices. This restriction holds simultaneously in every direction. The unresolved global test only needs forests satisfying all eight restrictions.

For 189 shapes an integer weighted inequality bounds the total edge count by at most 103. The remaining 27 have independently checked resolution refutations, comprising 24, two and one cases at 62, 63 and 64 vertices. An unrestricted opposite-face positive control on 117 vertices reconstructs an actual forest after the component allowance is raised to 32. [Coverage and individual certificates](dense-facet-audit.json), [audit and replay program](dense_facet_audit.py), [explicit control](dense8-positive-control.json).

The weighted inequalities use blocks of upper vertices consisting of three-dimensional subcubes and single vertices with all their neighbours. Inside each block we enumerate every possible selected subset. Together with the fixed lower face it must have maximum degree two and contain no cycle. A weighted score assigns numbers to occupied vertices and induced edges. Each block contributes at most its largest score over its valid subsets. When all block inequalities are added together, each upper horizontal edge must receive unit weight; each upper copy of a fixed lower vertex must also receive unit weight for its crossing. A separate multiple of the known upper vertex count is allowed. Any positive deficit on a feature is charged in full because that feature can occur at most once. The final certificate checks the sum in integers on every literal block. Linear programming chooses the weights and the exact integer check establishes each bound. [Local configurations](forest_weight_bound.py), [weight generator and integer checker](forest_orbit_weights.py).

### Seven paths in the eight-cube occupy at most 116 vertices

Suppose an eight-cube forest on 117 vertices had at most seven components. It would have at least 110 edges. The 216 exclusions above already force each seven-face to have at most 61 vertices. At population 61 the full cube symmetry group gives 1,630 shapes. Of these, 1,593 lie in one of six half-full templates. Allowing any three deletions in each template gives edge bounds of 103, 100, 108, 101, 109 and 74, respectively, for both faces together. For each of the other 37 shapes a fixed-face inequality gives at most 103. Thus every seven-face has at most 60 vertices. [All 61-vertex shapes](seven-face-classes-61.txt), [family and exceptional bounds](seven-component-limit.json).

The two sides of each cut must therefore contain 57 and 60 vertices, or 58 and 59. Their component counts sum to at least 9+12=21 or 10+11=21. The eight cuts contribute at least 168 components. Counting by vertices and edges instead gives at most 117+7×7=166. This contradiction excludes 117 vertices. Any larger forest can be shortened to exactly 117 by removing tips or isolated vertices, so the bound of 116 holds for every forest with at most seven components.

If a nine-cube snake crosses a coordinate 13 times, its 14 runs split seven per side. It consequently has at most 232 vertices and 231 edges. Together with the uniform 110-edge bound for each half, this shows that **every coordinate in a 233-edge snake would change at least 14 times**. [Exact arithmetic and certificate replay](seven_component_limit.py), [uniform bound](DENSE_FACE_COMPONENTS.md).

To recover the shape counts, compile the stream enumerator and run it with arguments `2 streammarked 5`. Run the [seven-cube canonicalizer](seven_face_classes.cpp) on each marked file, passing an input and output filename. It computes one representative per signed coordinate permutation orbit and checks that each orbit weight multiplied by its stabilizer size is 645,120. There are 1,630 shapes at 61 vertices, 17,737 at 60 and 186,864 at 59. Testing which additional cube sites preserve an induced linear forest gives 5,134,080 maximal labelled forests at 61 vertices, 117,938,688 at 60 and 670,000,128 at 59. [Stream totals](stream-marked59-census.txt), [classification and maximality verifier](dense_face_catalogue.py).

The variable-template inequalities retain the population of each face, allow every deletion pattern of the specified size, and average over symmetries of the template. On each representative block the verifier enumerates all allowed induced subsets in both layers and checks the rounded weights in integer arithmetic. Running `python seven_component_limit.py --replay` checks all six template certificates and all 37 exceptional fixed-face inequalities. At the original target of 104 edges, templates 0, 1, 3 and 5 already exclude 555 of the 1,630 shapes together. [Variable-template verifier](variable_facet_weights.py).
