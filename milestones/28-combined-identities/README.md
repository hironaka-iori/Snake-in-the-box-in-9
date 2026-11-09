# Combining the global identities on the k6 / k7 full products

Run of 9 November 2026, 14:55 to about 20:00, at `nice -n 10` on at most 2 cores (peak RSS 4.4 GB,
for the k7 product). Solver and Python side, plus one toy Lean file. No certificate was replayed and
no Lean module of the chain was built.

**Answer.** With every solver result known (old and new), the corner-share identity alone, used as
an edge weight `120 sym + S5` on the Lean k6 full product, gives **m <= 233** (stage B). The w3 census
never helps: the LP optimum puts weight 0 on it in every data state. With certified data only, the
bound stays **235**.

Stage A (the identities, their Lean statements, the window data, and which data are certified) is in
`INVENTORY.md`.

## Method (stage B)

`comb.py` builds the product exactly as the Lean k6 check enumerates it (`../23-k6-lean/full_product/fp.py`,
34 shapes x 6^5 counts, canonical labels). It applies every known plain UNSAT key. Each allowed
transition (step n: directions d(n)..d(n+7), counts a(n+2)..a(n+7), new count s = a(n+7)) carries:

- `A = s`, the lumped alpha of the new vertex;
- `S5`, a lower bound on the M = 12 share sum of the trailing 5-window (centres n+3..n+7), from the
  share oracles of milestone 11, the Lean floors of origin/main, and this run (0 where unknown);
- `W6`, a lower bound on the w3 charge sum of the 6-window (centres n+2..n+7), as in
  `../22-global-arguments/k6_w3_loop/fullprod.py`.

For integers a, b >= 0 the step weight is `w = a (120 A + S5) + b W6`. Each 5-window and each 6-window
is the window of exactly one step. With shares and c >= 0, alpha >= 1 at vertices 1..6, alpha >= 4 at
the endpoints, and c >= c1 = 257 at the 36 multiplicity deficits:

    sum_n w(n) <= 5a (219960 - 840 m) + b (387072 - 36 c1)

    (P + 4200 a Q) m <= Q (1099800 a + b (387072 - 36 c1)) + 7 P + R          (*)

Here lambda = P/Q is the minimum cycle mean of w on the full product (vectorised Howard, `comb.howard`),
and R is the range of the integer Bellman-Ford potential on all allowed transitions. With a = 1, b = 0
and S5 = 0, (*) is the k6 alpha chain (milestone 23) multiplied by 120. `lp.py` searches the ratio b/a
(golden section on the Lagrangian dual of the frequency LP) and verifies the best point exactly.
`k7comb.py` does the same on the k7 product of milestone 25 (44.6 M transitions, closed-set rule).
There the constants are 1099680, 8P and 42 c1.

## Results

### Sanity checks

| check | expected | here |
|---|---|---|
| alpha only, keys_235 | lambda 4, range 5, 13 BF rounds, 235 | **lambda 4, range 5, 13 rounds, 235** |
| alpha only, all known k6 keys | 65/16 (235.35) | **65/16, 235.35** |
| alpha only, k7 keys_best234 | lambda >= 6423/1544, 234; 44,649,358 transitions | **lambda 4.16 (104/25), range 5.28, 234; 44,649,358** |
| w3 only, all known keys | lambda6 = 1630 (k6_w3_loop fullprod) | **1630**; with the exact arithmetic (*) this is m <= 238 (k6_w3_loop's informal 7 + 63148/mu said 239.45) |
| known sets (`adversary.py`) | real snakes are at the floor | 20 bank snakes: floor 191.2 for every mix (v = 192); adversary 208: 207.2 (share) to 209.2 (w3); adversary 224: 223.3 to 224.8 |

### Bounds (`data/b_*.json`, `data/k7_*.json`)

| plain keys | share data | w3 | LP optimum | lambda (alpha units) | real m | bound |
|---|---|---|---|---|---|---|
| certified (1,383: r4b, r4c, keys_235) | none | no | alpha | 4 | 235.72 | 235 |
| certified | Lean floors (main) | no | share | 4 | 235.72 | **235** (certified-only answer) |
| all known solver keys (28,615) | none | no | alpha | 4.0625 | 235.35 | 235 |
| all known | none | yes | alpha + 0.107 w3 | | 235.23 | 235 |
| all known | Lean floors only | no | share | 4.0958 | 235.16 | 235 |
| all known | all oracles before this run | yes | **share, w3 weight 0** | **4.25** | 234.26 | **234** |
| k7 keys_best234 | all oracles before this run | yes | share | 4.1667 | 234.83 | 234 |
| k7 pool (every known k6/F8/H9 key) | all oracles before this run | yes | share | 4.25 | 234.34 | 234 |
| all known + this run's | all oracles + this run's | yes | **share, w3 weight 0** | FINAL | FINAL | **233** |

Before this run the binding 4-cycle of the share weight (alpha 2,5,5,5) had never been tested. It sat
in the "4.25 region" that no earlier loop visited, because those loops chased the alpha-only cycles
near 4.0.

### The refinement (`loop.py`, `bulk.py`)

`loop.py` works on Howard's minimum cycle of `120 A + S5`. For each window on it, it runs a plain
6-window test, then a plain 5-window test, then a share threshold at the next level of
16/24/48/72/108/150/200. `bulk.py` tests the transitions that violate a Bellman-Ford potential computed
with optimistic shares. Most binding windows were plain-UNSAT 6-windows that solve in 0.02-3 s.

FINAL TABLE

## Stage C: binding cycle and ceiling

FINAL

## Stage D: certificates, cost and Lean glue

FINAL

## Files

| file | contents |
|---|---|
| `comb.py` | product, weights, vectorised Howard, Bellman-Ford, the arithmetic (*) |
| `lp.py` | the LP / Lagrangian search over (a, b) and the exact check |
| `k7comb.py` | the same on the k7 product (`best` = keys_best234, `pool` = all known keys) |
| `loop.py`, `bulk.py`, `solvers.py` | the share refinement (plain, share-threshold and w3 calls) |
| `ceiling.py`, `adversary.py`, `need.py` | stage C: witnessed ceiling and what-if, known-set floors, deficits of a potential |
| `certplan.py` | stage D: certificate list and cost for a target lambda |
| `lean/CombinedShareToy.lean` | stage D: the combination lemma (core Lean, standard axioms) |
| `data/oracle_plain*.jsonl`, `data/oracle_share*.jsonl`, `data/oracle_w3.jsonl` | every new solver call |
| `data/loop_rounds.jsonl`, `data/bulk_rounds.jsonl` | rounds |
| `data/b_*.json`, `data/k7_*.json`, `data/c_*.json`, `data/certplan_*.json` | results |
