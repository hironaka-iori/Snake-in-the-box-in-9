# Combining the global identities on the k6 / k7 full products (LP over local frequencies)

Run of 9 November 2026 (in progress; this checkpoint is updated at the end of the run).
Solver and Python side only; no Lean module was written or built.

See `INVENTORY.md` for stage A (identities, Lean statements, window data, certified vs solver-only).

## Checkpoint results (stage B, before the refinement loop)

Bound = largest m allowed by the exact arithmetic of `comb.py` (*) with the Bellman-Ford potential
range R on all allowed transitions of the full product.

| plain keys | share data | w3 | best combination | lambda (alpha units) | real m | integer bound |
|---|---|---|---|---|---|---|
| keys_235 | none | no | alpha | 4 | 235.72 | **235** (sanity: milestone 23) |
| all known (28,615) | none | no | alpha | 65/16 = 4.0625 | 235.35 | 235 (sanity: milestone 23 share_bonus) |
| all known | none | yes | alpha + 0.107 w3 | | 235.23 | 235 |
| all known | Lean floors (main) | no | share | 4.0958 | 235.16 | 235 |
| certified (1,383) | Lean floors (main) | no | share | 4 | 235.72 | 235 |
| all known | all oracles | yes | **share only (w3 weight 0)** | 4.25 | 234.26 | **234** |
| k7 keys_best234 | none | no | alpha | 4.16 | 234.86 | 234 (sanity: milestone 25) |
| k7 pool | all oracles | yes | share | 4.25 | 234.34 | 234 |
