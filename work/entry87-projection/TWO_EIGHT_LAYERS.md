# Joining long induced paths in two eight-dimensional faces

A 193-vertex snake that crosses a coordinate exactly once splits into two induced paths in opposite eight-dimensional faces. Each arm has at most 99 vertices. The three possible unordered size pairs are 99+94, 98+95 and 97+96. Translate the common crossing address to zero. The two projected arms meet at zero, and any further shared address produces an unwanted edge. Hence disjointness away from zero is exactly the remaining condition, once each arm is induced.

We extracted eight-dimensional subpaths from six eight-dimensional parents, 1,173 nine-dimensional paths, and 34,802 higher-dimensional records. This produced 239 initial forms. Six completed endpoint-regrowth searches expanded the menus. Both orientations and all subpaths of the required size are allowed. Each rooted shape is normalized by the order of first use of its coordinates. The join enumerates distinct relative coordinate assignments for the second arm. [Catalogue](eight-face-catalogue.json), [extraction and join driver](two_eight_layers.py), [complete size tests](two-eight-layers-expanded.json).

| Arm sizes | Rooted shapes in the two menus | Placements with 0, 1, 2, 3, 4 extra contacts |
|---|---:|---:|
| 99+94 | 2 × 23,860 | 0, 0, 0, 0, 0 |
| 98+95 | 14 × 9,220 | 0, 0, 0, 0, 0 |
| 97+96 | 102 × 2,606 | 0, 5, 0, 25, 93 |

The 97+95 positive control recovers a valid 191-edge snake. A separate near-contact run directly reconstructs each of the five one-contact placements and checks every vertex pair. As a check on the counting rule, all counts from a short two-direction example agree with literal enumeration of coordinate assignments. The coverage is the explicit menus above. A new pair of arms would require at least one rooted shape outside its corresponding menu. [Near-contact census and samples](near-face-pairs-1-4-250.json), [count and witness validation](near_face_pairs.py).

To reproduce the native tools, compile `extract_seven.cpp` as `extract-eight.exe`, `seven_regrow.cpp` as `eight-regrow.exe`, and `mixed_halves.cpp` as both `join-eight.exe` and `near-face-pairs.exe` with a C++20 compiler. Run `python two_eight_layers.py --build`. The six completed regrowth runs use `python seven_regrow.py SIZE TRIM --dim 8 --bank eight-face-catalogue.json --nodes 160000000` with (SIZE,TRIM) equal to (94,24), (95,29), (96,32), (97,37), (98,41), and (99,45). Run `python near_face_pairs.py --expanded --contacts 4 --samples 250` to reproduce the table.
