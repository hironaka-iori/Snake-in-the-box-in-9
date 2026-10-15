# Joint layer search checkpoint

Date: 15 October 2026. Verified bounds remain 191 <= a(9) <= 254; the conjecture 196 is unresolved.

`work/joint_layer_search.py` selects both Q8 induced paths jointly, with exact lengths and a common endpoint at zero. Their projected vertex sets may intersect only at zero. A circuit constraint with an auxiliary vertex enforces connectivity; all selected adjacent cube vertices must be consecutive. The first directions can be normalized to coordinates 0 and 1 because they must differ.

The final implementation matched all 42 independent exhaustive comparisons in Q2 and Q3, including both feasible and infeasible cases with and without symmetry. A fixed Q8 benchmark also passed. These controls are evidence about the implementation, not a Lean proof of the solver model.

The benchmark comes from bank index 0. Its Q9 path crosses coordinate 5 once, at edge index 96. Its projections have 96 and 94 edges and intersect only at their joining endpoint. `JointLayerSeed.lean` checks the two paths, every cross-pair equality, normalization, and the 191-edge join through the existing integer layer theorem. It also proves that the two neighbors adjacent to a compatible join cannot coincide. This is a decomposition of a published example, not a new record.

| Layer lengths | Joined target | Hint | Time limit | Outcome |
|---|---:|---|---:|---|
| 98, 97 | 196 | None | 120 s | UNKNOWN |
| 98, 98 | 197 | None | 120 s | UNKNOWN |
| 96, 95 | 192 | Checked 96,94 pair; neither path fixed | 120 s | UNKNOWN |

All runs used four workers and random seed 13. No longer witness or impossibility certificate was obtained. Branch/conflict counts and exact elapsed times are stored in the JSON records. The current one-crossing family is a restriction on general Q9 paths, even when both projected paths are free.

Reproduce from the repository root with Python 3.12 and the pinned OR-Tools dependency:

```sh
python work/joint_layer_controls.py
python work/extract_joint_seed.py
python work/joint_layer_search.py --left 96 --right 94 --seconds 10 --hint outputs/joint_layer_seed.json --fixed-to-hint --output outputs/joint_layer_191_control.json
python work/joint_layer_search.py --left 96 --right 95 --seconds 120 --hint outputs/joint_layer_seed.json --output outputs/joint_layer_192_seeded.json
python work/joint_layer_search.py --left 98 --right 97 --seconds 120 --output outputs/joint_layer_196.json
python work/joint_layer_search.py --left 98 --right 98 --seconds 120 --output outputs/joint_layer_197.json
```

The first two long searches preceded the addition of optional hints, so their records omit hint-specific fields; they used no hint. The fixed benchmark record has `fixed_to_hint: true`; the other searches do not fix vertex sets. Preserve old result files before repeating a run. The 15-module core builds with `lake build` in `work/final_lean`.

Next experiments should compare diverse compatible seeds or permit multiple crossings. Repeating the same 120-second run cannot resolve the current uncertainty without additional search or a changed method. The fixed 98-edge seed's previous exclusion does not apply to the 96,95 target or to other variable pairs.
