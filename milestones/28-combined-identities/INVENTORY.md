# Stage A: the global identities and the window data that bound them

Everything below was read on 9 November 2026 from this branch (`research/unconditional-241`) and, for
milestones 35, 152 and 155, from `origin/main` (35 from the local ref; 152 and 155 through the GitHub
contents API, because the main pack is larger than the free disk).

## Identities

| identity | Lean statement (file) | per-vertex quantity | in Lean? |
|---|---|---|---|
| **alpha** (square census, `T + 2 s0 = 9214 - 35 v`, `s0 >= 0` dropped) | `countSeq_facts` (`work/spectral/stronger/AggregateWindowConditional.lean`): `4 <= a0, 4 <= am, 1 <= a(j)`, `a0 + sum a(j+1) + am + 35 (m+1) <= 9214`; used as `sumA (m-1) + 35 m <= 9171` in `AggregateDirection6Conditional.upper_of_windows6` | `alpha(x)` = singleton squares at x (automaton: `sym = min(alpha, 6)`) | yes |
| **corner share** (the same census with `s0` charged to selected neighbours) | `core_charge_sum_le` (`work/spectral/stronger/ShareBridge.lean`): `sum_{k<=m} (2M coreAlpha k + coreShare M k) + 70 M (m+1) <= 18428 M`; with M = 12: `sum (24 alpha + share12) + 840 (m+1) <= 221136` (`work/spectral/ShareCharge.lean` underneath) | `share12(x) = sum over unselected neighbours q of floor(12 e0(q)/d(q))` | yes. Since share >= 0 it **implies** the alpha identity, so in any combination alpha is redundant once share is used |
| **3-cube census** | not in Lean. Double counting (`milestones/22-global-arguments/README.md` section 5): `sum_x w3(x) + E3 = 5376`; integer form `sum_x c(x) <= 64512`, `c(x) = sum_{3-cubes Q ∋ x} floor(12/|Q cap S|)` | `c(x)` (12 c = 1 w3) | **no** (the census lemma itself is still to be written; "easy" per milestone 22) |
| **three-square share bonus** | `snake_occurrence_bonus` / `pair_share_packing` + `pattern_share_in_snake` (origin/main, milestone 35): for N occurrences of 0123415 in a snake, `sum share12 >= 6 N` | a lower bound on `sum share12`, i.e. a second inequality on the same share quantity | yes (main) |
| **share-16 / share-17 floors** | origin/main milestone 152 (`012032`, universal) and milestone 73 (`012031`, `012304`, `012314`): every fitting 5-centre window with that canonical shape (either orientation) has `sum_{5 centres} share12 >= 16`; milestone 155: `012032` with counts `(4, <=4, 4, <=5, 3)` (or reversed) has share sum `>= 17` | window lower bounds on `share12` | yes (main) |

The three-square bonus and the share floors are not new identities: they are certified window data for
the corner-share identity. In LP terms the bonus is a second lower bound on the same `sum share12`,
so it enters as a convex combination with the window bound, never as a sum (milestone 35's own warning).
Milestone 23's `share_bonus/README.md` already showed that it does not touch any binding cycle of the k6
product; it is not used below.

## Window data

| data | quantity | files | status |
|---|---|---|---|
| plain exclusions, radius 4 | alpha (exclusion) | `10-window-aggregate/data/oracle_cache*.jsonl`, `11-local-ceiling/k6_loop/oracle_plain.jsonl`, `s0_share_loop/share_oracle.jsonl` (plain records), `s0_k6_ceiling/oracle5_extra.jsonl`, `oracle6.jsonl`, `22-global-arguments/k6_w3/data/plain_k6w3.jsonl`, `k6_w3_loop/data/plain_loop.jsonl.gz`, `23-k6-lean/full_product/oracle_full.jsonl`, k7: `25-k7-234/data/oracle_k7.jsonl.gz`, `oracle234.jsonl.gz`, `decide234.jsonl` | **certified**: `direction_certificates_r4b/r4c.json` (237/236 replays) and `keys_235.json` (235, Lean end to end), together 1,383 keys. A handful of k6_w3 / s0_k6_ceiling keys are drat-trim verified but not replayed. The other ~27k k6 keys, all H9/F8 keys and keys_best234's 9,784 new keys are solver answers |
| 5-centre share thresholds (M = 12) | `sum share12` over 5 centres | `11-local-ceiling/s0_share_loop/share_oracle.jsonl` (2,003 calls), `s0_radius4/*_results.jsonl` (E1 seeds), `k6_loop/oracle_share.jsonl`, `s0_k6_ceiling/oracle5_extra.jsonl` | solver only, except the share-16/17 floors above (Lean, main) |
| w3 thresholds | `sum c` over 5 or 6 centres | `22-global-arguments/w3_survey/data/w3_alpha_oracle.jsonl`, `k6_w3/data/w3_k6_oracle.jsonl`, `k6_w3_loop/data/w3_loop_oracle.jsonl`; sub-window DP floor and single-centre minima (`w3_survey/refine_w3.Sub`) | solver only (and the identity itself is not in Lean) |

New solver calls of this milestone are in `data/oracle_plain.jsonl`, `data/oracle_share.jsonl` and
`data/oracle_w3.jsonl` (same record formats).
