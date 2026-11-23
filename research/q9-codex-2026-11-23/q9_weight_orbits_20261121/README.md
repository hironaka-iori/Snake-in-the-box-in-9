# Orbit lifts of grouped coordinate weights for the nine-cube

For a seed walk p, choose a translation t and a partition of the nine coordinate axes into disjoint sets. At each time i and for each group G, prescribe the number of set bits in (p[i] xor t) restricted to G. Then freely choose a representative of that weight in every group, subject to an induced path globally. The group actions can differ from one time to the next. With four two-axis groups, four coordinate transpositions can operate independently throughout a path. Larger groups allow arbitrary permutations within each group. The earlier binary-isometry experiment offered only two full placements at a given index.

The SAT instance uses one variable for a candidate group value in each run between successive changes to that group. On consecutive vertices, exactly one group changes in weight, so every other group is constant. The changing group must flip one bit. At nonconsecutive times whose group weights differ by total Manhattan distance greater than one, the full vertices are already far enough apart. For smaller distances, clauses forbid attaining the lower bound simultaneously in all groups. The initial group values can be fixed up to a groupwise coordinate permutation.

All four target runs use the 800 local ordered 192-edge walks with one chord. The coordinate partition, translation and input row are sampled; duplicates are possible. A model would supply an explicit 192-edge witness. UNSAT applies only to that concrete weight profile. UNKNOWN denotes a conflict-budget stop. The larger-budget run reuses 48 of the original 5+4 cases. Summary rows are stored as ordered JSON lists of trial, input row, group bit masks, translation, solver status, conflict count and witness. The local verification script checks all inputs and every returned path by computing pairwise distances. A deliberately damaged 191-edge path has two chords and is reconstructed by both the grouped-run encoding and a separate per-time vertex-domain encoding. The independent verifier also re-encodes the first sixteen initial UNSAT cases per group. The files contain solver outcomes rather than externally certified UNSAT proof traces.

Run from this directory using Python with python-sat and its CaDiCaL 1.9.5 backend:

```sh
python -B search.py 234 1 193 12000 --control > control.json
python -B search.py 22221 2000 149293 2000 > shape22221.jsonl
python -B search.py 333 1700 1739 2400 > shape333.jsonl
python -B search.py 432 1700 49991 4000 > shape432.jsonl
python -B search.py 54 500 50193 4000 > shape54.jsonl
python -B retry.py > retry54.jsonl
python -B verify.py > verified.log
```

## Results

The four initial runs returned no 192-edge path. Both 1,700-case runs and the 2,000-case run returned UNSAT in every case. For the 500 cases with group sizes 5 and 4, 81 returned UNSAT at the initial budget. Of the 48 retried cases, 37 more returned UNSAT. Counting one final result per original trial gives 5,518 UNSAT and 382 UNKNOWN across 5,900 trials. Of the 64 first-pass negatives independently re-encoded, 57 were independently resolved UNSAT and 7 reached the independent conflict budget. Both encodings passed the 191-edge positive control.
