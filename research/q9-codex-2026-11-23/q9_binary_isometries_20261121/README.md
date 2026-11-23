# Binary coordinate placements of near-snakes

Both searches use the 800 ordered walks in `q9_onechord_expanded_800.txt` and aim at 192 edges. Each walk visits 193 distinct cube vertices and has exactly one nonconsecutive adjacent pair.

For two ordered placements P and Q, choose P[i] or Q[i] independently at every index i. If Q[i] together with P[j] breaks the required distance relation or repeats a vertex, choosing Q[i] forces Q[j]. When the unique chord of P joins a and b, every solution chooses Q[a] or Q[b]. Starting with each endpoint, take the closure of these implications. If the closure includes both endpoints of the chord of Q, that choice is impossible. Otherwise the closure itself is a solution. This decides the full two-choice family for these ordered placements. A valid mixed path switches placements at least once, so translations without an admissible consecutive crossing are excluded immediately.

In the first search Q is a translated coordinate permutation of P. Every one of the 512 translations was included, as were the identity, the 36 coordinate transpositions, the 168 three-cycles and 64 sampled other permutations. For the two orientations of this shared chord, the closure must omit the opposite endpoint. The 110,182,400 configurations yielded no 192-edge witness. In the second search Q comes from another row, possibly reversed. At a sampled index, coordinate labels are matched by the order of their nearest transition along each parent. All translations are tested for that alignment. Across 80,000 draws (repeats possible), 40,960,000 translation cases yielded no witness. The draws do not exhaust all parent pairs, alignments or cube paths.

The controls deliberately introduce a chord into a known clean 191-edge path. For the mixed-parent control, the chords are at opposite tips in the two damaged parents. Both programs reconstruct valid 191-edge paths. Independent Python checks all unordered vertex pairs in each control output and in each research input. The logs report solver searches, without independently checkable formal negative certificates.

From the parent workspace on macOS with the system clang++ and libc++, run

```sh
clang++ -O3 -std=c++20 q9_binary_isometries_20261121/search.cpp -o /tmp/q9_binary_isometries_20261121
clang++ -O3 -std=c++20 q9_binary_isometries_20261121/cross.cpp -o /tmp/q9_binary_cross_20261121
/tmp/q9_binary_isometries_20261121 3 64 800 923 < q9_onechord_expanded_800.txt
/tmp/q9_binary_cross_20261121 80000 53131 800 < q9_onechord_expanded_800.txt
PYTHONDONTWRITEBYTECODE=1 python3 q9_binary_isometries_20261121/verify.py
```

