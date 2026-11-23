# Two independent bridges and four rigid arcs

The selected input consists of the 34 rows marked 2 in `q9_new189_nearmisses.words`. Each row gives an ordered, distinct-vertex 192-edge walk with two extra edges between nonconsecutive vertices. The direct experiment retains a sampled clean central interval in its existing coordinates. Moving outward on either side, two nonempty rigid subarcs undergo independent coordinate permutations and an intervening connector takes arbitrary coordinate steps. Each isometry translates its starting point onto the preceding endpoint. Steps are placed one at a time and respect all selected central and arm vertices. The two completed arms are then checked for mutual overlaps and adjacency using 512-bit sets. Search limits apply separately to each arm. The first search uses 50,000 sampled cases, 6,000 DFS nodes per side and 48 stored arms per side.

The second experiment removes the three outermost vertices on each side before applying this construction. Each compatible pair now gives a 186-edge path. Symmetry representatives under coordinate permutation, translation and reversal are processed once. For each retained body, unrestricted legal tip steps extend the two ends up to a combined six edges. All splits between the two ends are explored by growing one end and then the other. These endpoint searches have no separate node cap. The second experiment uses 55,000 sampled cases, 8,000 nodes per side and 64 stored arms per side.

The positive controls repair a 191-edge walk with two deliberately injected chords and independently regrow the original reference class from a truncated 186-edge path. Python rechecks all 34 selected inputs and all emitted paths by pairwise Hamming distances and compares the recovered 191-edge classes against the 131-row reference file. A negative search result has no implication for unrestricted nine-dimensional paths.

Run from the workspace root on macOS with the system C++20 compiler.

```sh
d=q9_two_gap_hinges_20261121
clang++ -O3 -std=c++20 "$d/search.cpp" -o /tmp/q9_two_gap_hinges_20261121
clang++ -O3 -std=c++20 -DTIP_SEARCH "$d/search.cpp" -o /tmp/q9_dual_gap_two_tips_20261121
clang++ -O3 -std=c++20 "$d/tip_control.cpp" -o /tmp/q9_two_gap_tip_control_20261121
python3 "$d/damaged_control.py" | /tmp/q9_two_gap_hinges_20261121 0 2000000 40000 6159
/tmp/q9_two_gap_tip_control_20261121 < q9_reordered_segments_20261120/reference191.words
/tmp/q9_two_gap_hinges_20261121 50000 6000 48 31093 < q9_new189_nearmisses.words
/tmp/q9_dual_gap_two_tips_20261121 55000 8000 64 83151 < q9_new189_nearmisses.words
python3 "$d/verify.py"
```

