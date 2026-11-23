# Q9 completions of fragments from two registered Q8 hosts

A HOST row gives donor identifiers, an eight-bit translation, the intersection size, and a permutation of axes. Donor A uses its registered coordinates in facet zero. An input bit at position d of donor B moves to position perm[d]. XOR the resulting Q8 vertex with the translation, then add 256 to place it in facet one. The projected overlap was independently reconstructed for every row of the placement source.

For every anchor the solver may choose additional vertices anywhere in Q9. The host union provides initial variable polarities. The tests require one connected induced path of at least 193 vertices. Fixed anchors are induced linear forests. Every accepted path is checked with all pairwise Hamming distances.

| Batch | Placement rows | Fixed sets | Fixed vertices |
|---|---:|---:|---|
| Stratified by the 12 overlap sizes, with 60 placements per size | 720 | 5,760 | 145, 154, 164 or 173 |
| Dispersed release, including every placement with overlap two or three | 9,835 | 9,835 | 145 or 154 |
| One randomized fixed forest per recorded placement | 106,435 | 106,435 | 145 |

The first batch releases contiguous portions of the two host paths, with some variants retaining crossings. The second batch repeatedly removes a point from a long remaining host fragment. The third batch samples anchors from both hosts after resolving their crossing conflicts. Every third-batch case stores its original source line, fixed-vertex bit mask, search outcome, and any witness in **allhosts.jsonl.gz**. Hexadecimal bit v corresponds to Q9 vertex v in all case files.

The actual positive fixture from placement line 103039 uses donor IDs 494 and 582, translation 64, permutation 01234765 and projected overlap three. The 194-vertex host contains only 190 vertices of the returned 192-vertex path. Q9 vertices 464 and 493 lie outside the full host. **real_control.jsonl** stores the full path and case ID. Both SAT encodings also recovered a genuine 191-edge path from a published-in-workspace reference fixture, with a deliberately incomplete phase hint.

**prepare.py** and **disperse.py** construct the first two batches. **run.py** accepts the solver, conflict budget and case file. **allhosts.py** constructs and solves the placement-wide batch. **audit.py** checks coordinates using the inverse permutation, verifies anchor topology and masks, aligns search logs, checks every control path and computes independent sufficient exclusions using degree and parity capacity. The results apply to the recorded anchors. Other choices of fixed vertices in the same placements and general Q9 paths remain open.
