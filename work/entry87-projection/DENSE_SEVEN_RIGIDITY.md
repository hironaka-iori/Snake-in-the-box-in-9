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

### Why each extension is unique

The 9,424 half-full forests have six shapes up to cube isometry. Relative to any one of them, the nearest different half-full forest removes at least eight vertices and adds at least eight. This follows by generating the full isometry orbit from each representative and comparing those six representatives to all 9,424 labelled masks. Thus two half-full forests intersect on at most 56 vertices. Every subset with 57 or more vertices is in at most one half-full forest. For population n between 57 and 64 the exact number contained in a half-full forest is therefore 9,424 times the binomial coefficient C(64,n).

We independently count all forests by joining opposite six-faces and testing the induced degrees and acyclicity. The denser of the two six-faces may be fixed up to cube isometry. To place the other side it suffices to retain one representative per orbit of the symmetry group fixing the first face. Its orbit size restores the number of labelled placements. The streaming enumeration constructs the opposite six-face from two five-faces. For 62 through 64 vertices the population and component histograms also agree with direct joins of the complete labelled six-face inputs. At 62 and 63 the subset count accounts for every forest. At 61 any possible extension to 62 would also extend to 64, proving maximality for every remaining 61-vertex forest. The verifier supplies a concrete maximal set and tests all other sites. [Enumerator](near_full_faces.cpp), [marked counts](stream-marked-seven-census.txt), [classification and orbit construction](seven_deletions.py), [distance and counting verifier](dense_rigidity.py), [exact results and maximal witness](dense-seven-rigidity.json).

### How this can improve the global bound

Suppose a nine-cube snake has 233 edges. The nine coordinate-use counts sum to 233, so some coordinate changes at most 25 times. Its two faces contain alternating runs of the path, and each has at most 13 components. At least one face contains at least 117 of the 234 vertices. Shortening its components at their ends gives an **eight-cube induced linear forest on exactly 117 vertices with at most 13 components**. Ruling out this single extremal configuration would prove that every nine-cube snake has at most 232 edges, since a longer snake has a 233-edge prefix.

Splitting such a 117-vertex forest along any coordinate leaves one seven-face with at least 59 vertices. For 62, 63, or 64 vertices the dense-face classification gives precisely 192, 18, or 6 shapes, respectively. To test a fixed shape, choose the opposite vertices freely, require maximum degree two, and require at least 104 induced edges, since a forest on 117 vertices and at most 13 components has at least 104 edges. Every cyclic component found is excluded explicitly. [Facet decision](dense_eight.py).

There is a further bound that uses no solver. A singleton in a seven-face can have at most one crossing. A two-vertex component can also have at most one crossing, since both crossings together would make a square. Consequently each such short face component contains a global endpoint of its path, counting an isolated global vertex twice. If one face contains t singleton or two-vertex components, the full forest has at least ceil(t/2) components. In particular, a face consisting of 32 disjoint edges forces at least 16 components. Even if up to eleven of its vertices are deleted, at least 27 short components remain. This excludes all these subsets in the 117-vertex test. The full global extremal configuration remains unresolved.
