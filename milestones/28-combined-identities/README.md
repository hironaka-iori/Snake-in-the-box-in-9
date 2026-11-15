# Combining the global identities on the k6 / k7 full products

Run of 9 November 2026, 14:55 to 20:30, at `nice -n 10` on at most 2 cores (peak RSS 4.4 GB,
for the k7 product). Solver and Python side, plus one toy Lean file. No certificate was replayed and
no Lean module of the chain was built.

**Answer.** With every solver result known (old and new), the corner-share identity alone, used as
an edge weight `120 sym + S5` on the Lean k6 full product, gives **m <= 233** (stage B). The w3 census
never helps: the LP optimum puts weight 0 on it in every data state. With certified data only, the
bound stays **235**.

**Update (section "Refinement toward 232").** With context share thresholds (the trailing 5-centre
share bounded inside the step's 7- or 8-direction window), the same chain gives **m <= 232** with solver data
(lambda = 13033/24 = 4.5253 alpha units, potential range 6.97; after the second run 7154/13 = 4.5859, still 232: 231 needs 4.678). The corrected witnessed ceiling of
5-window shares is 230.1.

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
  killed it. **[Corrected in "Refinement toward 232": this was an artefact. `ceiling.py` did not read
  this milestone's own plain-SAT records, and a second `fp.Status()` in one process misses
  `k6_loop/oracle_plain.jsonl`. With both fixed, the period-3 family is still witnessed and the
  5-window ceiling is 230.1, not 223.5.]** It is now the 14-cycle of `../11-local-ceiling/s0_k6_ceiling` (alpha 6+,5,3,4,3,3,6+,…),
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


## Refinement toward 232

Run of 9-10 November 2026, 20:13 to 02:10, at `nice -n 10` on one core (peak RSS 1.2 GB for the k7
product, 0.6 GB otherwise). There was a container restart at 22:15; the loop resumed from the committed
records. Solver side only. **Result: m <= 232 with solver data**, at lambda = 13033/24 = 543.04
(4.5253 alpha units). 231 is out of reach of this loop.

### What changed

- **Context share thresholds** (`share7.py`). The step weight needs a lower bound on the share sum of
  the trailing 5 centres n+3..n+7. Milestone 28 took it from the 6-direction 5-window alone. Here it can
  also come from the longer window of the same step: ctx 7 (directions ds[1:8], the step's 6 counts) or
  ctx 8 (ds[0:8], with the count at n+1 free). In both, the share totalizer covers only the trailing 5
  centres. The class is `SubShareEncoding`, which is `wincert_share.ShareEncoding` restricted to a range
  of centres, with the same clause kinds. Every step has exactly one such window, so
  `S5 = max(5-window lb, ctx lb)` stays a lower bound and the arithmetic (*) is unchanged. A ctx
  record is oriented (no reversal). `comb.build` and `k7comb.edges` apply them; set `NOCTX=1` to switch
  them off.
- **`loop3.py`** is `loop.py` on one core, with these per-window steps: 6-window plain test (run in
  the step's orientation, so that a SAT model also gives the ctx-7 trailing-share witness), 5-window
  plain test, 5-window threshold, and then, if the 5-window is stuck at its witness or at a timed-out
  level, a ctx-7 threshold and after it a ctx-8 threshold. Timed-out levels are retried once at 600 s.
- **`eval232.py`**: the exact bound (*). It runs Howard on the live core, then integer Bellman-Ford on
  all allowed transitions at lambda_t = lambda and at quarter values below it. 232 needs
  `226 lambda_t > 121200 + R/Q`, which is about 540 for R of about 830.
- **`level_needs.py P/Q`**: the key and threshold sets one potential uses (see below).

### Rounds (`data/loop232_rounds.jsonl.gz`, 118 rounds, 5.3 h of loop time)

| time | round | lambda (alpha) | real m | bound |
|---|---|---|---|---|
| 20:21 | 0 | 4.4675 (11258/21) | 233.01 | 233 |
| 21:12 | 20 | 4.4826 | 232.93 | 233 |
| 22:18 | 40 | 4.4965 | 232.84 | 233 (lambda_t 539, R 804: margin 614 is too small) |
| 22:41 | 60 | **4.5007** (49148/91) | 232.82 | **232** (lambda_t 540, R 820 < 840; `data/b_232_r60.json`) |
| 00:18 | 87 | 4.5126 (28700/53) | 232.75 | 232 (lambda_t 1083/2, R 1652/2) |
| 01:57 | 118 | **4.5253** (13033/24) | 232.68 | **232** (lambda_t 543, R 837 = 6.97 alpha; `data/b_232_final.json`) |

New solver calls: 2,049 UNSAT, 1,042 SAT and 60 timed-out 6-windows; 761 SAT and 13 timed-out
5-windows (`oracle_plain_r232.jsonl.gz`). 5-window share thresholds: 258 UNSAT (117 at 16, 91 at 24,
39 at 48, 8 at 72, 3 above 100), 76 timeouts and 1 SAT (`oracle_share_r232.jsonl.gz`). Context
thresholds: 400 ctx-7 UNSAT (45 at 16, 180 at 24, 127 at 32, 23 at 48-60, 25 above 72), 22 timeouts
and 3 SAT; 8 ctx-8 UNSAT and 4 timeouts; plus 1,042 ctx-7 witnesses from the 6-window models
(`ctxshare_r232.jsonl.gz`). Solver time: 1.5 h on 6-window plain tests, 2.0 h on 5-window thresholds,
and 1.3 h on context thresholds.

### Key and threshold sets per level (`data/level_*.json`)

`level_needs.py` fixes one Bellman-Ford potential and lists what it uses. It counts the shares needed
on allowed transitions, split into those covered by main's Lean floors, by 5-window thresholds and by
context thresholds. For each excluded transition it would otherwise violate, it counts one plain key:
the shortest known UNSAT suffix window, chosen greedily, so this count is an upper bound for that
potential. "new" means a key found in this section.

| level | lambda_t, R | share uses (main floors) | 5-window share keys (by needed T: <=16/24/48/72/108/more) | ctx keys (same bins) | plain keys (3/4/5/6/7 directions; 7-dir new) |
|---|---|---|---|---|---|
| 233 | 520, 624 | 637,050 (585,476) | 1,105 (233/169/142/13/513/35) | 107 (18/47/32/5/2/3) | 15,790 (4/43/266/2,957/12,520; 601) |
| 232 | 543, 837 | 551,204 (513,627) | 1,143 (250/181/147/14/515/36) | 279 (37/123/95/9/10/5) | 28,733 (4/43/266/2,958/25,462; 1,951) |

At 233 the context keys are not needed: milestone 28 reached 233 without them. The table lists them
because this potential uses them. At 232 the potential needs 1,143 RefutedShare thresholds, 279 ctx
thresholds (a new certificate type: RefutedShare with a centre range, ctx 7 or 8) and about 28.7 k
plain keys. Of the plain keys, 1,951 are new 6-count keys; nearly all of the rest are solver keys that
were never replayed.

### Why it slows, and what helps

- **Context windows are what break the stall.** With the context records switched off (`NOCTX=1`,
  `data/b_232_noctx.json`), lambda stays at 6980/13 = **4.4744** (233). That value did not move from
  00:18 to 02:00: every gain after it came through ctx-7/8 thresholds. On the old 5-window ceiling
  cycle (below), 7 of the 12 ctx-7 thresholds at T = 5-window witness + 1 are UNSAT (`ceilctx232.py`).
  So 7-direction share windows do lift cycles that no 5-window certificate can lift.
- **w3 still gets weight 0** (`lp.py all all 1`, `data/b_232_share_w3.json`). Every b > 0 lowers the
  bound (232.751 at b = 0, 232.752 at b = 0.001). The binding windows carry only the w3 DP floors,
  1632-1639.
- **Three-square bonus.** The pattern 0123415 occurs once on the 53-cycle of 00:18. That is worth at
  most 30 share units, or 0.005 alpha, and less as a convex combination, so it was not used. **Share
  16/17 floors** (main) are already in. They cover 93 % of the share uses at both levels.
- **k7 product** (`k7comb.py pool all 0`, `data/k7_pool_all_0.json`, 37.1 M transitions, all
  F8/H9 keys and every context record). At the 00:18 data it gives lambda = 9208/17 = **4.5137**
  (bound 232, R 6.47 alpha), against 4.5126 on k6. The k7 keys add 0.001: the binding windows are
  untested, not k7-limited.
- **Binding cycle at the end** (`stall232.py`, `data/stall_final_cycle.json`). It has 96 steps, A mean
  4.40, S5 mean 15.5. On 64 steps the 6-window is untested, and only 5 steps are fully witnessed (6-window
  plain-SAT, 5-window witness and ctx-7 witness). 22 steps carry a timed-out level. The loop is still
  limited by missing tests, not by a witnessed obstruction. But the cycles get longer (30-100 steps
  instead of 3-40) and the timeouts more frequent. The rate fell from 0.015 alpha/h (first 2 h) to
  0.008 alpha/h (last hour).
- **231 needs** `225 lambda > 125400 + R/Q`, which is lambda > about 561 = **4.676 alpha** with R of
  about 840. That is 0.15 alpha above what was reached, about 20 h at the current rate, and the rate is
  falling.

### Ceiling

- **5-window shares + k <= 6-count plain keys** (`ceiling.py ceiling` with the reader fixes,
  `data/c_ceiling_232.json`). The witnessed ceiling is the period-3 family 0123014/0123042/0123412,
  lambda 7175/12 = 4.983, **m >= 230.1**. With this data type no bound below 230 is possible. The
  earlier 223.5 (`data/c_ceiling.json`) came from a witness set that was missing this milestone's own
  SAT records.
- **With context thresholds** that family is not a ceiling: 7 of its 12 ctx-7 windows prove more than
  the 5-window witness. The ctx-7-witnessed transitions (3,386, only those with a trailing-share
  witness from this run's models) carry a single live 3-cycle at lambda 6.539 (m >= 221.7). That is a
  valid but very loose ceiling for ctx-7 + k6. No ctx-8 witnesses exist.
- Realistic outlook: 232 is in hand with solver data. 231 needs about 0.15 alpha more and probably
  thousands more ctx-7/ctx-8 thresholds at T = 48-108, where the timeouts sit. The local ceilings
  (230 for 5-window shares, about 222 for w3 and loose ctx-7 witnesses) are far below the lower side.

### Second run toward 231 (10 November, 02:21 to 08:46, 2 workers)

`loop4.py` is `loop3.py` with the tests of each phase on 2 worker processes. It runs plain tests at
60 s, thresholds at 120 s and long retries at 1,800 s. Untested 6-windows come first. It also fixes the
second-`Status` reader. New records are in `data/*_r232b.jsonl.gz`, rounds in
`data/loop232b_rounds.jsonl.gz`.

| time | round | lambda (alpha) | real m |
|---|---|---|---|
| 02:22 | 0 | 4.5253 | 232.68 |
| 04:01 | 50 | 4.5444 | 232.57 |
| 05:56 | 100 | 4.5630 | 232.46 |
| 07:45 | 150 | 4.5778 | 232.38 |
| 08:45 | 169 | **4.5859** (7154/13) | 232.33 |

- **Exact result** (`data/b_231try_final.json`): **m <= 232**, at lambda_t = 7154/13 with R = 7.61 alpha.
  231 needs lambda > (125400 + R/Q)/225, which is **4.678 alpha**. The run got 0.06 of the 0.15 it
  needed, at 0.0094 alpha/h (6.4 h), so about 10 h more at that rate.
- **Calls:** 2,897 6-window UNSAT, 969 SAT and 22 timeouts; 596 5-window SAT; 426 5-window share
  thresholds UNSAT (73 timeouts, 8 SAT); 744 ctx-7 and 59 ctx-8 thresholds UNSAT (20 timeouts). No
  round was left without a cheap test, so the 1,800 s retries were never triggered.
- **Level set at lambda_t = 550** (`data/level_550_1.json`, R 902, bound 232): 1,355 5-window share
  keys (by needed T: 335/230/206/31/515/38), 728 ctx keys (54/321/263/60/24/6), and 31,532 plain keys,
  of which 4,742 are new 6-count keys. Main's floors cover 524,639 of the 567,506 share uses.
- **Binding cycle at the end** (`data/stall_final_cycle.json`): 52 steps. On 44 of them the 6-window
  is untested, none carries a timeout, and only one is fully witnessed. Missing tests still limit the
  bound. The extra lambda came mostly from cheap 6-window exclusions and from ctx-7 thresholds at
  T = 24-48. Without the context records, lambda is 4.4795 (233).
- The ceilings are unchanged: 230.1 for 5-window shares, and a loose 221.7 for ctx-7 (6,830
  ctx-7-witnessed transitions, still only one live 3-cycle).

### Files of this section

| file | contents |
|---|---|
| `share7.py` | context share encoding (`SubShareEncoding`), records, application to the product |
| `loop3.py`, `loop4.py` | the refinement with context thresholds (one core; 2 workers) |
| `farm231.py` | the refinement on several machines (section "Farm toward 231") |
| `eval232.py` | exact bound (*) with lambda_t search |
| `level_needs.py` | key and threshold sets of one potential |
| `stall232.py`, `ceilctx232.py` | binding-cycle census and the ctx-7 test of the 5-window ceiling cycle |
| `data/oracle_plain_r232.jsonl.gz`, `data/oracle_share_r232.jsonl.gz`, `data/ctxshare_r232.jsonl.gz` | every new solver call (context records are kept outside the `oracle_share` prefix) |
| `data/loop232_rounds.jsonl.gz` | rounds |
| `data/b_232_*.json`, `data/level_*.json`, `data/k7_pool_all_0.json`, `data/c_ceiling_232.json`, `data/stall_final_cycle.json` | results |

Caveats specific to this section: every number below 233 rests on solver answers (plain keys, share
and context thresholds). Context thresholds need a centre-range version of the RefutedShare bridge,
which does not exist yet. `loop3.State` inherits the second-`Status` reader bug, which only causes
repeated tests, never wrong exclusions. Bounds are always computed in a fresh process (`eval232.py`).

## Farm toward 231

`farm231.py` runs loop4's tests on several machines at once (this machine plus cloud containers). It is
a symmetric worker with no coordinator; the workers exchange their result files through git branches.

### Design

- **Epoch** (`--epoch-min`, default 8). Sync (below), then `loop4.State` is rebuilt from every record:
  the committed data files that loop4 reads, plus every file in `data/farm231/` (the farm records are
  hooked into `comb.own_plain_unsat`, `comb.share_records`, `share7.records` and loop4's
  second-`Status` reader). The rebuild takes 6-8 s and 0.3 GB, so it is done from scratch every epoch.
  Then Howard (0.5-1 s), a line in `data/farm231/rounds_w<I>.jsonl`, and the publish of this worker's
  files.
- **Candidates.** Integer Bellman-Ford (`comb.bellman_ford`) at lambda on the live core gives a potential
  phi (0.4-0.6 s) and reduced costs rc(e) = Q w(e) - P + phi(u) - phi(v) >= 0. Small rc alone means
  little: every edge of the shortest-path forest has rc = 0 (77,655 such edges at 7154/13). So the
  order is: the minimum cycle's steps first, then the edges of the **live core of {rc <= d Q}** for
  d = 0, 1, 2, 3, 4, 6, 8, 12, ... weight units (an edge in that core lies on near-cycles of mean about
  lambda + d), and inside a level the cheap kinds first, then rc. Each edge gets loop4's first open
  test of its step: (A) untested 6-window plain, (B) never-solved 5-window plain, (C) when
  lambda + `--margin` (default 12, i.e. the 231 level) - 120 A > S5, one threshold: the 5-window at its
  next level, else ctx 7, else ctx 8 (`loop.next_T`, `loop3.next_level`). The list stops at
  `procs * epoch_min * 60 / 8 * 3` owned tests (720 for 4 x 8 min); building it takes about 1 s.
- **Partition.** A test is run only by worker `int(sha1(key).hexdigest(), 16) % W`, where the key is
  the window (k6, k5, or (ctx, dirs, t)) without the level. One worker owns the whole ladder of a
  window, so two workers never run the same test, even when they are out of sync.
- **Run.** A fork pool of `--procs` processes runs `loop4.work`; the solver processes append their
  records to `data/farm231/{plain,share,ctx}_w<I>.jsonl` (loop4's formats) and the results are applied
  to the in-memory state as they arrive. Every `--regen-s` seconds (60), lambda, phi and the candidate
  list are recomputed from the updated state, so the next level of a window is queued right after a
  success and a test made moot by an exclusion is dropped. Long retries (1,800 s, loop4's phase D)
  start only when a worker has no owned candidate, at most procs - 1 at a time. The worker exits when
  `--hours` is over, free disk is below 300 MB, or `data/farm231/STOP` exists or arrives through sync.
- **Sync through git** (the `xfer233.py` approach: temporary bare repositories under `$FARM_SCR`,
  default `~/.farm231`, the working tree's branch is never touched). Worker I pushes
  `refs/heads/xfer/231/w<I>`; each commit holds `plain/share/ctx/rounds.jsonl.gz` and `record.json`,
  with the previous tip as parent (fast-forward only, never forced). Each epoch the worker runs
  `git ls-remote` on `refs/heads/xfer/231/*` and fetches (depth 1, one call, exactly those refs) the
  branches whose tip changed; the peers' files go to `data/farm231/<kind>_w<J>.jsonl.gz`. At start a
  worker merges its own branch's files into its local files (union of lines), so a restart, or a fresh
  machine with the same index, continues where its predecessor stopped; a foreign tip of its own
  branch is merged the same way before the next push. Network and push errors are logged and retried
  (3 tries, backoff), and the worker carries on.
- **Control.** `farm231.py stop` pushes `record.json {"stop": true}` to `xfer/231/ctl`; every worker
  stops at its next epoch. `farm231.py stop --clear` pushes `{"stop": false}`. A local
  `data/farm231/STOP` that came from ctl is re-decided at the next start; a hand-made one blocks.
- `farm231.py status`: sync, rebuild, lambda, m_real, the exact bound (`eval232.exact_best`, about
  10 s), per-worker record counts and the latest round line of each worker.
  `farm231.py merge`: all farm records, sorted and deduplicated, into
  `data/oracle_plain_r231.jsonl.gz`, `data/oracle_share_r231.jsonl.gz`, `data/ctxshare_r231.jsonl.gz`.
  `comb.share_records` and `share7.records` read these two share files (the plain glob already matches
  the first), so the merged data loads without the farm directory.

### Worker setup (fresh clone)

This machine can push `xfer/231/*` branches through the session's proxy (tested: create, fast-forward,
ctl). Branch deletion is refused here (HTTP 403), so the branches stay after the run. Everything
`farm231.py run` reads is tracked in git (checked with a Python audit hook in a sparse worktree that
held only the paths below: every file opened was tracked, and lambda matched). No cache needs a
rebuild. Python packages: `numpy` and `python-sat` (`pysat.solvers.Cadical153`, the CaDiCaL 1.5.3
library inside the wheel; no solver binary is called). `git` must be installed.

```
# full clone (1.7 GB checkout) or the sparse one (8 MB):
git clone --depth 1 --filter=blob:none --sparse -b research/unconditional-241 \
    https://github.com/hironaka-iori/Snake-in-the-box-in-9 snake && cd snake
git sparse-checkout set --no-cone /milestones/28-combined-identities/ /milestones/23-k6-lean/full_product/ \
    /milestones/23-k6-lean/scripts/ /milestones/11-local-ceiling/ /milestones/10-window-aggregate/scripts/ \
    /milestones/10-window-aggregate/data/oracle_cache.jsonl /milestones/22-global-arguments/
pip install numpy python-sat
cd milestones/28-combined-identities
nice -n 10 python3 farm231.py run --index I --workers 7 --hours H      # I = 1..6 on the cloud machines
```

This machine runs `--index 0`. Each worker needs about 0.4 GB for the main process plus the solver
processes (well under 1 GB each); 4 cores x 4 processes. Run `farm231.py status` anywhere to watch.
At the end: `farm231.py stop`, wait one epoch, `farm231.py status`, `farm231.py merge`, and commit
the three `*_r231.jsonl.gz` files.

### Test runs (15 November, this machine, 4 processes, `nice -n 10`, about 55 min in total)

| run | settings | lambda (alpha) |
|---|---|---|
| start | | 4.5859 (7154/13), loop4's last value |
| 1 | W = 1, 0.2 h, 3-min epochs | 4.5905 (12119/22) |
| 2 | restart of 1, 0.05 h | 4.5920 (12674/23); no test repeated (0 duplicate keys) |
| 3 | W = 7, index 0, sparse worktree, 0.04 h | 4.5931 (3307/6); every new test owned by worker 0 |
| 4, 5 | W = 1, 0.33 h and 0.17 h, 5-min epochs | **4.6012** (3865/7), m_real 232.246 |

- Exact bound at the end (`status`, and `eval232.py` on the merged files without the farm
  directory): **m <= 232** at lambda_t = 3865/7, R = 7.83 alpha; 231 needs 4.679 alpha.
- 1,741 tests, 2.74 solver hours: 6-window plain 1,420 (68 % UNSAT, 31 % SAT, 1 % timeout, mean 2.1 s),
  5-window plain 71 (all SAT), 5-window thresholds 88 (81 % UNSAT, 5 % SAT, 15 % timeout, mean 34 s),
  ctx-7 thresholds 151 (95 % UNSAT, 5 % timeout), ctx-8 11 (10 UNSAT). New records are in
  `data/*_r231.jsonl.gz` and on `xfer/231/w0`.
- Throughput: 16-40 tests/min with 4 processes (about 40 when 6-windows dominate, 16 when thresholds
  do); lambda rose at about 0.019 alpha/h, twice loop4's 0.0094 alpha/h on 2 processes. Most tests
  were speculative (off the minimum cycle: with W = 1, 23 of the 270 candidates of the first epoch were
  minimum-cycle steps). Whether 7 machines scale this further depends on how useful the tests far from
  the minimum cycle are; the rounds files will show it.

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

### Result of the farm run (2026-11-15): solver bound m <= 231

Fourteen workers (56 solver processes; one local machine and 13 cloud containers) ran
`farm231.py` for about 2.6 hours. The minimum cycle mean rose from 7154/13 (4.5859 alpha) to
**15268/27 (4.7123 alpha)**, and `eval232.py`, run on the merged record files alone, gives the
exact bound **m <= 231** at every one of its 13 test values of lambda_t (best: lambda_t = 15268/27,
R = 26450, slack 23050). The merged files hold 30,818 plain, 2,971 five-window share and 25,903
context-share records (`data/*_r231.jsonl.gz`).

This is a SAT-solver statement only. Nothing here is certified in Lean: the formal result of
this repository remains the unconditional bound 233.

One scheduling fault was found and fixed during the run (commit f743ca9e): phase-D long retries
ran only when no speculative candidate was left, which never happens, so the farm stalled at
1678/3 for 40 minutes once every step of the minimum cycle had only timed-out levels. Long
retries on the minimum cycle now take priority. Known open fault: a worker does not exit on
SIGTERM (use the STOP flag, or SIGKILL by PID).

## Certificate plan for 231

Stage B of the Lean 231 (15 November). The question: which certificates does a Lean chain for
m <= 231 with ONE potential need, how many, and what do they cost? Scripts: `certplan231.py`
(plan), `certsample231.py` (measured LRAT sizes, on cloud workers), `split231.py` (farm runner for
the solver tests that the plan asks for). Data: `data/certplan231_*`, `data/certsample231_*`,
`data/split231_jobs*`, `data/oracle_plain_cp231.jsonl`, `data/*_s231.jsonl.gz`.

### Answer

All figures are on the final data (farm round 2 merged, 615cc86f; split rounds 1-2), calibrated by
1,301 measured proofs, with every certificate at most 60 M replay hints (233's largest was 38.8 M
hints, 6.91 GB RSS). Kernel-hours and `.olean` use the MEASURED 233 ratios (209.84 kernel-h and
8.87 GB for 3.34 G hints).

| plan | lambda_t, bits, range | certificates (plain seeds / 5-win / ctx-7 / ctx-8) | hints (90 % range) | kernel-h | new .olean | .olean files |
|---|---|---|---|---|---|---|
| **232** | 541/1 (4.508 alpha), B = 10, 852 of 1,023 | **4,515** (3,099 / 948 / 404 / 64) | **8.2 G** (8.1-9.5) | 518 (509-595) | **21.9 GB** (21.5-25.2) | ~9,000 |
| **231** | 563/1 (4.692 alpha), B = 10, 1,022 of 1,023 | **12,084** (7,266 / 1,581 / 2,797 / 440) | **33.0 G** (32.8-37.9) | 2,075 (2,063-2,385) | **87.7 GB** (87.2-101) | ~24,200 |
| 231 alt. | 566/1 (4.717 alpha), B = 10, 1,021 of 1,023 | 13,454 (7,697 / 1,668 / 3,475 / 614) | 40.5 G (40.5-46.6) | 2,547 | 108 GB | ~26,900 |
| 233 (built) | 520/1 | 3,127 | 3.34 G | 209.84 | 8.87 GB | 6,254 |

Plain counts are seeds: the paid plain keys (231: 16,559; 232: 6,666) reduced by 233's measured
L1/L2 family ratio (2,637 seeds for 5,673 keys, 0.888 of the hints). On top of the new
certificates each chain imports what it reuses from 233 (up to 8.87 GB, 6,254 files, and the 1,042
floor modules).

**Consequence.** The single-process audit of 233 imported 8.87 GB of `.olean` at 11-12.6 GB RSS on
a 13.35 GiB machine. 231 needs about 10 times that, 232 about 2.5 times. Neither fits one audit
process on this machine. 232 might fit a machine with about 48-64 GB of memory; 231 needs a
different audit structure (separately audited premise modules) or far more records.

Breakdown by kind (calibrated G hints): 231 at 563/1: plain 17.5, 5-window 6.1, ctx-7 6.2,
ctx-8 3.3 (at 566/1: 19.2, 7.1, 9.0, 5.2); 232: plain 6.1, 5-window 1.6, ctx-7 0.45, ctx-8 0.15.
Distribution (231 at 563/1, before the family factor): 14,157 certificates under 1 M hold 2.8 G,
5,811 of 1-10 M hold 23.3 G, 481 of 10-60 M hold 9.1 G; the top 1 % / 5 % / 20 % hold 16 % /
38 % / 82 %. The bulk is thousands of 1-10 M certificates, not a tail: splitting
the tail does not make 231 cheap.

### Method (`certplan231.py`)

milestone 31's engine (`eng233.World`: full k6 product, 6,158,592 transitions, every known plain
key, warm Bellman-Ford with undo, dual reverse-delete, exact drops), extended:

- **Three share sources.** Step weight `120 s + max(L5(k5), L7(k7), L8(k8))`: `k5 = lkey(ds[2:8],
  t[1:6])` (both orientations, as share6), `k7 = (canon(ds[1:8]), t)`, `k8 = (canon(ds[0:8]), t)`
  (oriented). One share id space; per transition the three ids. The dual pass visits share ids by
  decreasing cost and lowers each to the largest need of the critical transitions that no plain key
  excludes and no OTHER source covers at its current level; the exact pass lowers by binary search
  against a warm Bellman-Ford. So one ctx record covers all its transitions, the kept level is the
  max over those that still depend on it, and the optimiser chooses per transition between
  "exclude by a plain key" and "raise a share level" (a plain key is dropped when its critical
  transitions are share-covered, and vice versa).
- **Free certificates** of the 233 chain: its 6,794 plain keys (5,402 of them in the pool here, plus
  the 1,383 replays), 9,498 keys L1/L2-derivable from its 2,637 widened seeds (families_k7 mirror),
  its 262 H8 cuts (exclusions), its 490 share thresholds up to their level, and main's floors 16/17.
- **Arithmetic.** m <= TARGET iff `(TARGET - 6) P - (1099800 - 4200 (TARGET + 1)) Q >= 2^B`
  (231: `225 P - 125400 Q`; 232: `226 P - 121200 Q`); B is the largest such bits value.
- **Pipeline** (`full P/Q`): calibration -> cap check on the full data -> dual -> derivable ->
  giants (milestone 31 step 3: longer suffix windows of the critical transitions only a big key
  covers, decided here at 20 s / 90 s, `data/oracle_plain_cp231.jsonl`) -> cap -> dual -> exact
  (all items, by decreasing calibrated cost) -> dual; the result is re-checked by a fresh full
  Bellman-Ford and saved as `data/certplan231_<tag>.json.gz` (production list: kind, key, level,
  proved level, source call (T, seconds), basis, est. hints) and `_summary.json`; `cost TAG` writes
  `_cost.json` (calibrated totals, bands, top 40).
- **Cap** (`--max-cert-hints`, default 6e7): plain keys above it leave the pool; a share id keeps the
  largest level whose certificate (re-solved there, priced by the level fit) is under the cap.

Level semantics: "UNSAT at T" proves share >= T, so every level <= T is implied; a lower level needs
a new solve at that level (cap = level - 1). The level-aware cost below assumes exactly these
re-solves; `data/split231_jobs_resolve232.jsonl.gz` (1,182) and `..._resolve231.jsonl.gz` (563/1 plan)
list them (split231 jobs, limit twice the source call). Nothing assumes a never-tried level above
a proved one.

### Calibration (measured, not fitted from old plans)

- **233 against milestone 31's model** (`calib233`, `data/certplan231_calib233.json`): share
  thresholds measured/model 1.27 in total (median 1.16, log-sd 0.43, 479 keys); plain seeds 1.06 on
  their own model (median 1.00), and 0.89 for all paid keys once families are counted. Replay hints
  are 0.54 of the trimmed full-proof hints (`est_hints`). Kernel: 0.13-0.17 ms/hint below 3 M hints,
  0.24-0.32 ms/hint above; replay RSS about 4-5 GB at 15 M hints and 6.9 GB at 39 M.
- **The 231 sample** (`certsample231.py`, 1,301 records on 10 cloud workers, all UNSAT, no timeout;
  stratified by source seconds with the whole slow tail; same toolchain as 233: CaDiCaL 2.1.3
  `--lrat --no-binary --unsat` on the full CNF, trimmed, then the replay portfolio on the core):

  | kind | n | measured / model (median) | replay / est | max hints | max CaDiCaL RSS |
  |---|---|---|---|---|---|
  | plain | 396 | 1.00 | 0.60 | 111 M (the 01203 giant: model 5.4 G) | 2.1 GB |
  | 5-window | 325 | 1.00 | 0.61 | 125 M | 2.2 GB |
  | ctx-7 | 396 | 0.82 | 0.59 | 106 M | 1.7 GB |
  | ctx-8 | 184 | 0.89 | 0.58 | 75 M | 1.3 GB |

  Share certificates follow `hints = A s^b (L/T)^c` (s = solver seconds of the source call at
  level T, L = the level re-solved): b = 0.93-1.04, **c = 3.41** (joint), log-sd 0.45-0.58 per
  certificate; A = 3.7e5 (5-window), 2.6e5 (ctx-7), 4.6e5 (ctx-8). Lowering a level is therefore
  worth a lot (L/T = 0.8 costs half). Plain keys use milestone 25's model with measured/model per
  log10 bin. The range is a bootstrap of the fit (5-95 %); per-certificate scatter averages out, so
  the range is narrow, and the systematic risk is the extrapolation of `(L/T)^c` below the sampled
  L/T (clamped at 0.4).

### Sensitivity and robustness

- lambda_t: on the dual pass (before exact) the cost is flat over 1125/2 .. 15268/27 (85-89 G,
  `data/certplan231_scan.json`), slightly cheaper at lower lambda_t. What decides is the slack:
  under the 60 M cap only lambda_t <= 566/1 works on the final data (the capped minimum cycle mean is
  about 4.722 alpha). The exact pass uses the whole range either way (1,021-1,022 of 1,023), and
  the lower lambda_t is cheaper: 563/1 costs 33.0 G against 40.5 G at 566/1 (fewer critical
  transitions, the same 10-bit potential); lambda_t below 563 was not run. More farm refinement helps mainly through slack (it moved
  the capped plan from infeasible to feasible between 07:03 and 08:10).
- 231 vs 232: one step of the bound costs a factor of about 5 in hints.
- ctx-7 only: infeasible. Without ctx-8 records the minimum cycle mean was 1640/3 = 4.556 alpha
  (data of 06:15) < 4.644 needed.
- Levels: maximum 200 (5-window), 150 (ctx), all <= 255 (8-bit fields).
- ctx families: of the 4,089 ctx certificates of the 231 plan, 3,172 distinct (ctx, dirs, t1..t5)
  groups: a lemma that widens the first count would save at most 22 % of the ctx certificate count
  (fewer if the cores do not allow the widening); 232: 429 groups for 468.

### The expensive tail and the long solver calls

Under the cap the largest certificates are 50-60 M (231: 654 between 10 and 60 M; 232: 78, the
largest 30 M). The top of the 231 plan are ctx-8 and 5-window shares from source calls of
160-280 s at level 35-72 (projected replay RSS 9-10 GB each, at the 233 trend). One needed level
rests on a source call over 600 s (5-window [[0,1,2,3,0,1],[4,4,5,4,5]] at 10, source T = 16 in
844 s); none rests on an 1,800 s call. Without the cap, 7 plain giants (model 0.7-5.4 G) and 15-18
share thresholds above 60 M were in the plan; the giants step replaced all plain giants by 6-window
keys (several hundred keys, ~0.5 G), and the cap plus split rounds 1-2 (452 solver tests on 7
machines) the shares.

### What the Lean chain must check for ctx records

For a ctx-c record (c = 7 or 8) with canonical directions `dirs` (c of them), counts `t` (the 6
lumped counts of the step's vertices n+2..n+7) and level L:

1. `RefutedShare` with a centre range: on the window `winOf dirs` with bounds `boundsOf t` (ctx 7) or
   `[(1,21)] ++ boundsOf t` (ctx 8; the count of vertex n+1 is free), M = 12, cap L - 1, the share
   totalizer over the TRAILING 5 centres only (share7.SubShareEncoding; certsample231's
   TaggedShareCtx is share233.TaggedShare with that centre filter). UNSAT means: every fitting
   window has share sum >= L over those 5 centres.
2. The bridge: for every step n of a snake, the ctx-7 window is the snake's directions d(n+1)..d(n+7)
   (ctx 8: d(n)..d(n+7)), relabelled by first occurrence, with the counts of n+2..n+7; its trailing 5
   centres are n+3..n+7, exactly the centres of S5(n) in milestone 28's (*). So `S5(n) >= L`, and
   the arithmetic of (*) is unchanged. The ctx-8 bound (1,21) needs `1 <= coreAlpha p (n+1) <= 21`.
3. Tables: one 8-bit level per (ctx, dirs, t), forward lookups only (no reversal); the step check is
   `P + pot(next) <= Q (120 s + max(share6, ctx7, ctx8)) + pot(current)` with the same potential and
   automaton as 233; each nonzero table field must be backed by a certificate at a level >= it
   (`RefutedShareFrom.anti` gives the lower levels).

### Assumed, not verified

- Plain families: the count and hint reduction of L1/L2 among the NEW plain keys is 233's ratio,
  not computed (it needs a widened core per key).
- Share costs below the proved level come from the level fit; the re-solves of the job files have
  not been run yet. A re-solve that times out marks an underestimated certificate.
- Kernel-hours and `.olean` scale linearly with hints at the 233 means; large certificates ran at
  1.5-2 times the mean ms/hint in 233.
- The greedy exact pass depends on its order: the counts are upper bounds for one potential, not
  minima. Every saved plan was re-checked by a full Bellman-Ford on all transitions, but not yet by
  the Lean generator's re-check on all labels.
- Records are solver answers; the farm's plain keys and thresholds still need their certificates
  (that is what is costed here).
