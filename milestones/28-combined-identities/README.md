# Combining the global identities on the k6 / k7 full products

Run of 9 November 2026, 14:55 to 20:30, at `nice -n 10` on at most 2 cores (peak RSS 4.4 GB,
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
| all known + this run's (30,209) | all oracles + this run's | yes | **share, w3 weight 0** | **11258/21 / 120 = 4.4675** | 233.01 (233.18 with R) | **233** (R = 6.64 alpha units, 154 BF rounds) |
| k7 pool + this run's | all oracles + this run's | no | share | 4.4683 | 233.09 | 233 |

Before this run the binding 4-cycle of the share weight (alpha 2,5,5,5) had never been tested. It sat
in the "4.25 region" that no earlier loop visited, because those loops chased the alpha-only cycles
near 4.0.

### The refinement (`loop.py`, `bulk.py`)

`loop.py` works on Howard's minimum cycle of `120 A + S5`. For each window on it, it runs a plain
6-window test, then a plain 5-window test, then a share threshold at the next level of
16/24/48/72/108/150/200. `bulk.py` tests the transitions that violate a Bellman-Ford potential computed
with optimistic shares. Most binding windows were plain-UNSAT 6-windows that solve in 0.02-3 s.

| | |
|---|---|
| time | 4.6 h wall (15:26-20:04), 1-2 cores (202 rounds; `loop2.py` runs a round's calls on 2 workers) |
| lambda of `120 A + S5` | 4.25 (round 0) → 4.3333 (round 20, first **233**) → 4.400 (17:15) → 4.4667 (round 202). The rate was 0.04 alpha units per hour at the end, and the loop was stopped on a 3-cycle at 536 whose windows time out |
| new plain calls | 4,057 6-window UNSAT, 212 5-window UNSAT, 906 6-window SAT, 915 5-window SAT, 84 timeouts |
| new share thresholds | 691 UNSAT (mostly T = 16, 24 and 48, which the k5 share loop never tried), 220 timeouts, 6 SAT |
| w3 | 6 threshold calls on the 4.311 cycle (2 UNSAT at 1660, 4 timeouts at 60 s). Its windows are as hard for w3 as for share |
| 232 needs | lambda > (121200 + R)/226, about 4.50 with R of about 6.6: 0.03 more than reached |

## Stage C: binding cycle and ceiling

- **The LP optimum never uses w3.** With the census added (`lp.py ... 1`), the golden-section search
  ends at b = 0 in every data state: 234.26 at the start, 233.59 at 16:28, and 233.01 at the end. The
  w3 lower bounds on the binding windows are the DP floors, 1624-1662, which are worth 238 alone, so
  any positive weight lowers lambda. With the share oracles switched off, w3 adds 0.12 edge to alpha
  (235.35 → 235.23 at b/a = 0.107). The complementarity the prompt hoped for exists only at the ceiling
  level, on witnessed cycles (the w3 ceiling cycle, 222.2, is a share-mediocre period-6 cycle). On the
  lower side the share data are simply denser, and the w3 lower bounds would need thousands of 6-window
  thresholds, which time out on the same hard windows.
- **Binding cycle at the end** (`data/b_final_share_w3.json`): 42 transitions, alpha mean 4.357, S5
  mean 13.2 (0.11 alpha). On 31 of its 42 transitions both the 6-window and the share are untested. So
  the lower side is still limited by missing tests, not by an obstruction. This is the situation of
  every share loop so far.
- **Witnessed ceiling** (`ceiling.py ceiling`, `data/c_ceiling.json`). Take the minimum over cycles whose
  every 6-window is plain-SAT and every 5-window has a share witness. Before this run it was the
  period-3 family 0123014/0123042/0123412, alpha 3,6,3,3,6,4, mu 4.98 (230.1). New 6-window exclusions
  killed it. It is now the 14-cycle of `../11-local-ceiling/s0_k6_ceiling` (alpha 6+,5,3,4,3,3,6+,…),
  mu = 5214/7/120 = 6.207, **m <= 223.5**. The witnesses are unminimised plain models, so this cap is
  loose. No set of 5-window share certificates and k <= 7 plain keys can lift that cycle on this
  automaton.
- **Known sets** (`adversary.py`). For every mixing weight, the floor is at least 207.2 (adversary 208)
  and 223.3 (adversary 224). Both identities are nearly tight on cycle unions, so the mix interpolates
  between 207.2 and 209.2 and never goes below the better identity. The 224-adversary is already
  refuted by five-centre radius-3 windows. The 208-adversary, which is plain-SAT at radius 4 with
  k <= 5, is the obstruction of every local combination: **about 207**.
- **5/6/7 centres.** k5 + shares: rigorous ceiling 230.9 (`s0_share_loop`). k6 + shares: lower side
  233.2 (this run), witnessed ceiling 223.5, heuristic (milestone 11, untested windows forcing 108)
  229.6 and rising. k7 (milestone 25 product, all known F8/H9 keys): the same lambda as k6 at today's
  data (4.4683 against 4.4675), because the binding windows are untested. k7's own cuts only matter
  once the k6 lower side is saturated. Realistic targets: about 230-231 for k6 + 5-window shares with
  tens of thousands of threshold tests; the k6 w3 ceiling (222.2) and the k6 share ceiling (223.5)
  bound anything local of this type from below at about 222.

## Stage D: certificates, cost and Lean glue (233 is below 234)

### Certificate list (`certplan.py 520`, `data/certplan_520_1.json.gz`)

The smallest lambda_t that still gives 233 is about 519.3, set by the range. Take lambda_t = 520 =
13/3 in alpha units. Bellman-Ford on the final data gives range 624 (5.2 alpha units, 15 rounds) and
bound 233 (the margin needed is 227·520 − 117000 = 1040 > 624). With this potential fixed:

| certificates | count | estimated LRAT hints |
|---|---|---|
| share keys needed | 11,800 | |
| covered by the Lean floors of main (share >= 16 on 012032/012031/012304/012314; the 012032 share-17 counts) | **10,804** | 0 |
| new share thresholds (RefutedShare, M = 12) | **996**, by needed T: 195 at 16, 130 at 17-24, 116 at 25-48, 39 at 49-100, 482 at 101-108, 34 above 108 (28 of them E1 seeds without a solve time, priced 0) | **15.5 G** (1.0 M hints per solver-second; median 6.3 M; the top 50 hold 5.7 G) |
| plain exclusions (greedy hitting set of 2.74 M critical excluded transitions, then reverse delete) | **15,169**: 1,266 already replayed (free), 51/1,554/12,298 new 4/5/6-centre keys | **31.2 G** = 16.0 G (591 radius-4 cache "giants", est_r4) + 8.0 G (7,046 keys at the class median 1.13 M) + 4.9 G (solve-time fit) + 2.3 G (this run's keys) |
| total, before any cost reduction | about 16,200 new | **about 47 G hints**: about 5,400 kernel-hours at 0.42 ms per hint, or 2,900 at 0.22; about 135 GB of olean at 2.9 B per hint; plus about 0.8 GB of Cnf/Sat modules (50 KB each) |

`share_samples.py` calibrated the share cost with 8 LRAT samples of this run (`data/share_samples.jsonl`):
12 k hints at 0.0 s, 0.71 M at 0.9 s, 1.41 M at 1.5 s, 3.45 M at 3.6 s and 6.64 M at 6.7 s. Two more
samples exceeded the 90 MB file cap. A model of 1 M per second follows. This is above the s0_share_loop
estimate of 0.5 M per second.

**How this compares.** The k7 234 set started at 34.3 G and fell to 1.73 G after milestone 25's
reduction steps: giant replacement by one-step extensions, re-solving the median-costed keys,
replacement by longer windows, and exact drops. The same steps apply here unchanged:

- 16 G sit in 591 radius-4 giants, which milestone 23's `extend.py` once replaced for almost nothing;
- 8 G are median-costed keys;
- many of the 996 share keys need a much lower T than the level that was proved (the needed T is
  known per key).

A realistic target after reduction is therefore a few G hints. That is a few times the k7 234 route,
for one more edge, and the reduction itself was not attempted here.

**What would still be missing.**
- Each of the 996 thresholds needs a certificate. They were solved only with the incremental
  wincert_share encoding.
- The 15,169 plain keys must be re-pruned on the final potential with exact drops, as milestones 23
  and 25 did.
- 204 new shards (`check6SAt`) must be built.
- The share-table cover and the Lean glue below.

### Lean glue (designed; the arithmetic part is prototyped)

The chain is the k6 chain of milestone 23 with one extra table. Every other piece exists.

1. **`Tables6S`** = `Tables6` plus a share table `sIdx : Nat → Nat` (5-window shape code to row) and
   `shr : Nat → Nat → Nat` (row, first count to packed fields at `cntIdx6` of the other four counts,
   in the format of `pot`). `check6SAt` is `check6At` with the step test
   `num + pot6 (c.drop 1) [t1..t4, s] ≤ den * (120 * s + share6 (c.drop 2) [t1, t2, t3, t4, s]) + pot6 (c.take 7) [t0..t4]`,
   where `share6` looks the window up in both orientations and takes the maximum. The shards are
   regenerated with the same 204-shard layout. The weight is wider (13-14 bits), but the per-transition
   work is one more lookup.
2. **Share bridge.** For each table entry (5-shape, counts) with value T, there is a
   `RefutedShare W bounds 12 (T-1)` certificate. `refuted_share_bridge`
   (`work/final_lean/LocalWindowShareBridge.lean`) turns it into
   `T ≤ Σ_{i<5} coreShare 12 p (r+i+1)` for every snake window with that canonical shape and those
   lumped counts. A `cover6S` lemma, the analogue of `cover6_rows`, checks that every nonzero table
   field is backed by a certificate. Entries covered by main's universal floors (milestones 73, 152,
   155) use those theorems instead.
3. **Sequence.** `invariant6S` / `total_bound6S` are copies of `invariant6` / `total_bound6` with the
   weight `120 * sym a(n+7) + S5 n`. They give
   `P (m-7) ≤ Q Σ_{n<m-7} (120 sym a(n+7) + S5 n) + (2^bits - 1)`.
4. **Combination** (`lean/CombinedShareToy.lean`, compiled with `lean -o`, axioms `propext`,
   `Quot.sound`). For arbitrary sequences, the telescoped inequality, the window bounds
   `S5 n ≤ share(n+3) + … + share(n+7)`, `sym ≤ α`, `4 ≤ α 0`, `4 ≤ α m`, `1 ≤ α j` and
   `Σ_{k≤m} (24 α k + share k) + 840 (m+1) ≤ 221136` (`core_charge_sum_le`, M = 12) imply
   `(P + 4200 Q) m ≤ 1099800 Q + 7 P + R` (`combined_bound`). With P/Q = 520 and R = 736 this gives
   `m ≤ 233` (`m_le_233`). In the real chain, `rsum` is replaced by the project's `psum`/`Finset.sum`.


## Caveats

- Every number below 235 rests on solver answers. That covers the ~29k plain keys beyond the 1,383
  replayed ones, all 5-window share thresholds except main's floors, and all w3 data. The w3 census
  itself is not in Lean.
- "Certified" share data means the floors proved on `origin/main` (milestones 73, 152, 155). Their
  Lean files are not on this branch.
- Like `fp.py`, the product enumerates canonical labels only. Labels above max+1 give the same
  transitions, so the Lean shards enumerating all 9 labels check the same inequalities.
- The certificate plan uses one potential and a greedy cover. Its counts are upper bounds for that
  potential, not minima.

## Files

| file | contents |
|---|---|
| `comb.py` | product, weights, vectorised Howard, Bellman-Ford, the arithmetic (*) |
| `lp.py` | the LP / Lagrangian search over (a, b) and the exact check |
| `k7comb.py` | the same on the k7 product (`best` = keys_best234, `pool` = all known keys) |
| `loop.py`, `loop2.py`, `bulk.py`, `solvers.py` | the share refinement (plain, share-threshold and w3 calls; `loop2` = 2 workers) |
| `share_samples.py` | LRAT size of share thresholds (cost model) |
| `ceiling.py`, `adversary.py`, `need.py` | stage C: witnessed ceiling and what-if, known-set floors, deficits of a potential |
| `certplan.py` | stage D: certificate list and cost for a target lambda |
| `lean/CombinedShareToy.lean` | stage D: the combination lemma (core Lean, standard axioms) |
| `data/oracle_plain*.jsonl`, `data/oracle_share*.jsonl`, `data/oracle_w3.jsonl` | every new solver call |
| `data/loop_rounds.jsonl`, `data/bulk_rounds.jsonl` | rounds |
| `data/b_*.json`, `data/k7_*.json`, `data/c_*.json`, `data/certplan_*.json` | results |
