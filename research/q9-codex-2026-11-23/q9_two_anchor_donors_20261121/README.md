# Two-anchor splicing between 191-edge donors

Each experiment takes a recipient path P and a different donor Q from the 131-row reference bank. The prefix P[0..a] stays in place. Translating the suffix P[b..191] by any nine-bit vector s is allowed. The inserted segment of Q is mapped by a coordinate permutation and translation, with both its endpoints pinned at P[a] and P[b] xor s. A replacement with g additional edges yields 191+g edges. Translating the suffix lets g be odd. Positive output is pairwise-checked by the C++ implementation.

If any vertex of the shifted suffix equals or is adjacent to a prefix vertex, a graft of at least two edges cannot fit. Remaining shifts must match both the Hamming distance and the parity of the donor endpoints. The solver matches the differing coordinate bits of the donor endpoints bijectively with those of the two anchors. The other coordinates map among the equal bits. Every partial assignment that determines a donor interior point, relative to either anchor, is checked against the closed neighborhoods of the exterior prefix and suffix vertices. Used donor coordinates are assigned in full and unused coordinates can be completed arbitrarily. The internal donor geometry, including adjacency to its anchors, follows from its isometric embedding.

The sampled forward-donor run covers requested gains from one to four and the sampled reversed-donor run covers gain one. Repeated random draws can repeat geometry. The five-window run takes recipient row zero and checks all 130 other donors, each in both directions, with every starting position, all suffix shifts, and all anchor-compatible coordinate permutations for those five windows and gain one. Search outputs are restricted to these families.

The positive control shortens the known first record by three edges using a translated suffix and reconstructs a 191-edge path from that valid 188-edge path and a donor fragment. Independent Python checks all parent and control paths. It recomputes the eligible shifts and donor counts in each fixed window and directly enumerates all 9! permutations for one eligible donor placement in each of the five windows. The remaining placements use the C++ branch pruning.

Reproduce from the workspace root with the host C++20 compiler.

```sh
d=q9_two_anchor_donors_20261121
bank=q9_reordered_segments_20261120/reference191.words
clang++ -std=c++20 -O3 "$d/search.cpp" -o /tmp/q9_two_anchor_donors_20261121
clang++ -std=c++20 -O3 "$d/five_windows.cpp" -o /tmp/q9_donor_five_windows_20261121
/tmp/q9_two_anchor_donors_20261121 0 1 842 < "$bank"
/tmp/q9_two_anchor_donors_20261121 20000 50 153161 < "$bank"
/tmp/q9_two_anchor_donors_20261121 150000 100 67423 reverse < "$bank"
/tmp/q9_donor_five_windows_20261121 < "$bank"
python3 "$d/verify.py"
```

