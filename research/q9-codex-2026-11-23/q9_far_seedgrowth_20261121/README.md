# Two-ended Q9 growth with borrowed excursions

The host consists of the two registered Q8 donors at the placement recorded in q8_near_host_placements.log. The input generator samples 850 placements in each projected overlap stratum from two through five. Other donors from the same registered clusters supply portions of both arms. The arms are joined at a shared column and shortened when another column would produce a chord. Additional roots come from intervals of validated 191-edge paths in the same coordinate frame and from a coordinate transposition on the terminal portion of promising intervals.

Each target instance fixes a contiguous induced interval, its host and its upper limit on host-external vertices. The two ends of the fixed interval may grow or stop at different times. All 512 vertices are available subject to the external cap, inducedness and the rooted interval. The search reuses the host-claw deletion bound and incremental occupation logic of q9_seed_growth.hpp. It additionally checks a generous reachable-vertex capacity bound periodically. Only a search that finishes its tree without a budget cutoff exhausts that fixed-root instance.

| Target batch | Roots | Root length in edges | First-pass cap per root |
|---|---:|---:|---:|
| Borrowed aligned donor pieces | 10,199 | 80–187 | 16,000 |
| Intervals of known paths | 110 | 124–183 | 45,000 |
| Transposed terminal pieces | 111 | 118–183 | 85,000 |

The external caps range from 6 through 15. The 1,134 initial cutoffs were retried at 340,000 nodes; the remaining 398 were retried at 1,360,000. Of 10,420 distinct target instances, 10,151 were exhausted and 269 remained limited. All three target batches and the retries together visited 691,415,305 nodes. No 192-edge path was returned.

Nine positive controls fixed 176-edge subpaths of known true 191-edge paths and recovered 191-edge solutions containing exactly 6, 8, 9, 10, 11, 12, 13, 14 or 15 host-external vertices. An independent left-then-right enumeration of 165 small fixtures agreed with the bounded solver. The target runs returned 19 different 191-edge path classes already represented in the local 131-class comparison bank. The one 189-edge class absent from the prior189 reference is in new189.words.

The .dat rows hold the original placement line number, exterior cap, base node cap, record tag, host size and sorted vertices, followed by root size and ordered vertices. Logs contain per-row node counts, cutoff flags and returned near-target paths. The final audit independently reconstructs each host from the recorded permutation and translation, verifies all root adjacency constraints and checks the full returned near-target sequences by pairwise distances. Broadening or removing the fixed interval creates a different search family.
