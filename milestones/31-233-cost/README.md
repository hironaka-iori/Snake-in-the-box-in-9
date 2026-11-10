# The certificate cost of a Lean-checked 233 (share-weighted k6 chain)

Run of 9–10 November 2026, about 20:10 to 02:20. It used one core at `nice -n 10` (peak RSS about
0.4 GB) and added under 2 MB of data. Solver and Python only: no lake and no Lean. Every LRAT proof
streamed through a FIFO into `lrattrim` and was never stored. The container restarted once (22:15);
the run resumed from the committed state.

**Answer.** Milestone 28's 233 route is the share-weighted k6 chain at λ = 520, i.e. 13/3 in alpha
units. After the cost reduction below it needs

> **3.21 G LRAT hints in 6,163 certificates**: 5,673 plain keys (including 262 H8 cuts)
> and 490 share thresholds, on top of the 1,383 replayed keys and main's share floors.
> At checker v3's 0.1 ms/hint that is **89 kernel-hours** (178 at 0.2 ms/hint), and about
> **8.0 GB of `.olean`** at 2.5 B/hint, plus about 0.3 GB of Cnf/Sat modules.
> With the family lemmas L1/L2 the cost is **3.00 G hints in 4,030 certificates**: 83 kernel-hours at 0.1 ms/hint (167 at 0.2), and 7.5 GB.

That is about **1.9×** the k7 234 set, which needs 1.73 G (2.0× with families on both: 3.00 G against 1.49 G), for one more edge. The first
estimate of milestone 28 was 47 G, so the reduction is about **15×**. The set is
`data/keys233_best.json.gz` and the summary is `data/cost233_best.json`.

## The bound being certified

With weight `w = Q (120 s + L(k5)) − P` on the allowed transitions of the Lean k6 full product, and
a Bellman-Ford potential of range at most `2^B − 1`, milestone 28's (*) gives
`(P + 4200 Q) m ≤ 1099800 Q + 7 P + 2^B − 1`. Here:

- `s` is the new lumped count;
- `L(k5)` is the certified share level of the trailing 5-window.

So m = 234 is excluded iff `227 P − 117000 Q ≥ 2^B` (`lib233.best_pq`, `bound233`). At P/Q = 520/1
with B = 10: `4720 m ≤ 1104463`, so **m ≤ 233**. The range allowed is 1,023; the best set uses
784. Every set below was re-checked by a fresh Bellman-Ford on all 6,158,592 transitions.

## Steps and what each saved

All numbers are LRAT hints of the Lean replays. Cost model:

| certificate kind | cost source |
|---|---|
| plain key | measured replay when available: milestone 25's `replay234.jsonl` (5.3 k keys) plus 14 here |
| plain key, otherwise | milestone 25's per-(centres, own-solve-time) bin means. 14 samples of milestone 28's own keys came out at measured/model = 1.00 (`data/calib233.json`) |
| share threshold | `hints = 3.60e5 · t^0.964`, t = the solve time of the threshold at a level ≥ the level used. Fitted on **27 replays** of share thresholds at their needed level, core + portfolio pipeline (`measure233.py`, `data/replay233.jsonl`). Milestone 28's model (1 M hints per solver-second) overestimated these 27 by **3.2×** |
| H8 cut | milestone 25's H bins |

| step | set | λ | plain paid | share paid | hints | saved |
|---|---|---|---|---|---|---|
| 0. milestone 28's plan as estimated | `certplan_520_1` | 520 | 13,903 | 996 | 46.7 G (old models) | |
| 1. the same plan, re-costed (measured + calibrated) | `recost520` | 520 | 13,903 | 996 | **24.3 G** (plain 19.4 G, of which 13.1 G in 7 radius-4 giants; share 4.9 G) | 22.4 G (model) |
| 2. cost-aware dual prune, full k6 product, share weight | `p520` | 520 | 15,471 | 996 | 25.5 G | (−1.3 G, but valid: range 624) |
| 3. giants by longer windows (one-step extensions, then 6-windows) | `g520` | 520 | 15,784 | 996 | 13.0 G | **12.6 G**: the 7 giants (13.1 G) replaced by 320 new 5/6-window keys (0.54 G) |
| 2′. re-prune on the newer pool (milestone 28's committed r232 exclusions + step-3 keys) | `p520b` | 520 | 15,599 | 1,067 | 18.7 G | |
| 3′. giants again | `g520b` | 520 | 15,718 | 1,067 | 13.4 G | 5.3 G |
| 4. **exact drops** (warm Bellman-Ford; plain keys and share levels interleaved by cost) | `x520b` | 520 | **5,416** | **492** | **3.80 G** | **9.6 G**: 10,302 keys dropped, 942 share levels lowered (367 of the 492 paid levels end below their proved threshold) |
| 5. λ choice | `x519`, `g524`, `p518` | 519 / 524 / 518 | 5,259 | 502 | 3.79 G at 519 | none: 519 equals 520 (range 31,447 of 32,767, no slack left); 524 is 25 % worse halfway through its exact pass; 518 cannot meet its range (594 > 585). **520 is kept** (Q = 1, B = 10, range 784 of 1,023) |
| 6. H8 cuts (the full 8-direction step window, first interior vertex uncounted, inside the k6 product) | `h520` | 520 | 5,673 (262 H8) | 490 | 3.77 G | 38 M (7 of 91 items replaced) |
| 7. share thresholds re-solved at the level used | `s520` | 520 | 5,673 | 490 | **3.21 G** (share 0.78 G) | **0.55 G** (share 1.34 → 0.78 G). Each paid threshold was solved again at the level the set uses (60 s limit, most expensive first). 5 timed out and keep their old cost |
| 8. main's Lean share floors | | | | | | **≈ 0.57 G and 12,058 certificates** (≈ 0.6 GB of Cnf modules). 12,058 of the 23,544 floor-covered 5-windows are used by the potential. 11,801 of them need at most 16. A sample of 20, solved at the needed level, averages 47 k hints (`data/floors_s520.json`). They cost nothing here |
| 9. families L1/L2 | | | | | | **0.21 G and 2,133 certificates** (L1 alone: 0.19 G and 1,843). These are milestone 30's widened cores and greedy cover on the paid k6 keys. Cores came from milestone 30 (the 234 set) plus 656 computed here; 2,242 keys in sibling groups still lack one, so this is a lower bound. Share thresholds are not widened: no `RefutedShare` analogue of `refuted_narrow` exists yet |

Notes on the steps:

- **Re-cost (1).** Half of milestone 28's 47 G came from two models. The share model was 3.2× too
  high. The plain keys were costed at a class median of 1.13 M, against milestone 25's measured
  bins (0.24 M for keys without a solve time, and bins by solve time otherwise). The plan as listed
  is also **not quite sufficient**. Its share list misses levels on transitions that it treated as
  covered by known share lower bounds, so the range is 1,024 against 1,023 allowed. Step 2 repairs
  this.
- **Dual prune (2).** This is milestone 25's reverse-delete with the potential fixed. Each
  transition with `Q·120 s − P + π(u) − π(v) < 0` must be excluded by a chosen key, or have
  `L(k5) ≥` the level it needs. Plain keys and share levels are visited by decreasing cost:
  - a plain key is dropped when its critical transitions stay covered;
  - a share level is lowered to what its uncovered transitions need.

  It converges in one pass (0.4 s). Exact drops show how loose it is.
- **Giants (3).** Each of the 7 giants is a 4-centre key on 01203 or a 5-centre key, priced at 0.67
  to 5.4 G from its radius-4 estimate (milestone 25's decide timed out at 60 s). Each is needed on
  24 to 1,242 critical transitions. Their longer suffix windows were decided (at 20 s, retrying
  timeouts at 90 s): 5-count windows mostly time out, while 6-count windows are UNSAT with a
  median of 0.47 s. The cheapest cover was added and the giant dropped by a warm Bellman-Ford, so a
  transition left uncovered can still be absorbed by the potential. All 7 were replaced, by 320
  keys in all. The share option (raising a proved level) was offered too, but it was never
  cheapest.
- **Exact drops (4)** carry most of the reduction, as in milestone 25. A removal is accepted when
  the warm relaxation keeps the range, and is rejected after 40 frontier rounds. Successes take
  under 1 ms and failures about 0.3 s, so a full pass takes about 32 minutes. A second pass on
  `x520b` dropped nothing in its first 800 items and was stopped.
- **λ (5).** The slack is `227 P/Q − 117000` weight units. With Q up to 64 it is almost the whole
  margin: 585 at 518, 799 at 519, 1,023 at 520, 1,927 at 524. Below 520 the pool cannot keep the
  range. Above 520 more transitions become critical. Unlike milestone 25, the cheapest point is not
  at the edge: 519 and 520 cost the same.
- **H8 (6)** is the in-k6 analogue of milestone 25's H9. The step window has 8 directions, so the
  vertex n+1 between d(n) and d(n+1) can be part of a window, uncounted. An H8 key is
  `Refuted (winOf dirs) (boundsOf syms)` with 6 bounds on a 9-vertex window, in milestone 25's
  reversed form with the uncounted vertex last. The automaton needs one more lookup per
  transition. 93 % of the 4,316 H8 windows decided were UNSAT. But every expensive share threshold
  had a few plain-SAT H8 windows among its transitions, so they stay. The saving is small (38 M).
  The same holds for k7: the binding share transitions are plain-feasible even with one more
  direction. This is why the k7 product (milestone 25, H9/F8) was not built with the share weight.
  It would also need about 3–4 GB on this machine's budget, and milestone 28 found the same λ
  there (4.4683 against 4.4675).

## The best set

| | value |
|---|---|
| λ | P/Q = **520/1** (13/3 alpha units). B = 10. Potential range **784** of 1,023 allowed. `4720 m ≤ 1104463`, so **m ≤ 233** |
| plain keys | **7,056**: 1,383 already replayed (free), **5,411 paid k6 keys** (9 with 4 centres, 1,344 with 5, 4,058 with 6) and **262 H8 cuts**. Together they hold **2.43 G hints**: the top 100 hold 0.67 G and the top 1,000 hold 1.99 G. The largest key costs 11 M hints (a 4-centre key on 01203, fitted, never measured); the median 66 k. 1,130 paid keys (0.33 G) have measured replays |
| share levels | **23,783** 5-windows carry a level. **23,293** of them are at or under main's Lean floors (free). **490 paid `RefutedShare` thresholds** hold **0.78 G**: the top 10 hold 0.18 G and the top 100 hold 0.56 G; the largest is 39 M (012304 / 3,5,3,4,6 at 48) and the median 0.60 M. By level used: 126 at 16 or below, 106 at 17–24, 110 at 25–48, 121 at 49–100, 27 above 100. 389 of the 490 use a level below the proved threshold |
| total | **3.21 G hints in 6,163 certificates**. That is **89 kernel-hours at 0.1 ms/hint** and 178 at 0.2 ms/hint. It is **8.0 GB of `.olean`** at 2.5 B/hint, plus about 0.31 GB of Cnf/Sat modules |
| with L1/L2 | **3.00 G hints in 4,030 certificates**: 83 / 167 kernel-hours, 7.5 GB. This is a lower bound on what families save, since only 3,169 of the 5,411 paid keys have a core |
| summary | `data/cost233_best.json` (with the whole chain) |

## Lean plan for the share-weighted chain

The chain is milestone 23's k6 chain (`WindowAutomaton6Defs`, `DirectionWindowBridge6`,
`AggregateDirection6Conditional`) with one more table, a second certificate type and a different
final identity. Everything below the automaton (the `Refuted` replays, `AllRefutedList`, the
bridges) is reused as it is.

### 1. Automaton (`WindowAutomaton6SDefs.lean`, a copy of `WindowAutomaton6Defs`)

- **`Tables6S`** = `Tables6` plus a share table:
  - `sIdx : Nat → Nat` maps a 6-direction (5-centre) shape code to a row;
  - `shr : Nat → Nat → Nat` maps (row, first count) to packed fields at `cntIdx` of the other
    four counts, in the format of `pot`, holding the level `L`.

  The table holds the levels of `data/keys233_best.json.gz` (`share`, column 3) plus main's floors.
  A field is the maximum over both orientations.
- **`share6 T c t`** looks the trailing 5-window up in both orientations and returns the larger
  value.
- **`check6SAt`** is `check6At` with the step test

  `num + pot6 (c.drop 1) [t1..t4, s] ≤ den * (120 * s + share6 (c.drop 2) [t1..t4, s]) + pot6 (c.take 7) [t0..t4]`.

  The potential uses `B` bits (`B = 10` at `P/Q = 520/1`). The weight needs 13 to 14 bits. Each
  transition costs one more table lookup. The 204-shard layout of `ShardsOK6` stays the same.
- **`invariant6S` / `total_bound6S`** are copies of `invariant6` / `total_bound6`. They give
  `P (m-7) ≤ Q Σ_{n<m-7} (120 sym a(n+7) + S5 n) + (2^B - 1)`.

### 2. Certificates: two types

| type | statement | checker | count (best set) |
|---|---|---|---|
| plain key (k6) | `Refuted (winOf ds) (boundsOf syms)` | the existing LRAT replay (checker v3) and `LocalWindowTags` clause soundness | see README |
| **share threshold (new for this chain)** | `RefutedShare (winOf ds) (boundsOf syms) 12 (L - 1)`: on every fitting window the M = 12 share sum of the 5 centres is at least `L` | the same LRAT replay on the share CNF (`wincert_share`: window + totalizers + `shareCl` + `shareCap`); clause soundness by `LocalWindowTagsShare` / `LocalWindowTagsSharePacked` (`Tags.soundS`, `checkAllS`) | see README |

- The LRAT replay of a share CNF is the same kernel computation as a plain one. Its Cnf/Sat module
  carries the share meaning tree and tags (`mtB64`, `tagsOfS`). A share core is 3 to 5 times
  larger than a plain core (8 k to 38 k clauses; `data/replay233.jsonl`).
- **`cover6S`** is the analogue of `cover6_rows`. Every nonzero field of `shr` at level `L` must
  be backed by one of:
  - (a) a `RefutedShare … 12 (L' - 1)` certificate with `L' ≥ L`, turned into
    `L ≤ Σ_{i<5} coreShare 12 p (r+i+1)` by `refuted_share_dir`
    (`work/final_lean/LocalWindowShareBridge.lean`);
  - (b) for `L ≤ 16` on 012032/012031/012304/012314, or `L ≤ 17` on the milestone-155 counts,
    main's universal floor theorems (milestones 73, 152, 155; their files are on `origin/main`
    and must be brought over).
- Plain keys merge as now, through `allRefuted_of_merge` of the 236/237/235 lists and the new
  chunks. With L1/L2 (`LocalWindowFamilies.lean`), the derived keys are one
  `refuted_key_of_wide` / `refuted_sub` term each.

### 3. Glue: share identity + automaton bound (differs from the k7 234 chain)

The 234 chain ends with the alpha aggregate `sumA (m-1) ≤ 9171 - 35 m`, which is
`countSeq_facts`, and `total_bound7`. The 233 chain replaces it with three pieces.

1. **Window bounds.** For every step n, `S5 n ≤ Σ_{j=n+3}^{n+7} coreShare 12 p j`. This comes
   from `cover6S` and `refuted_share_dir` (or a floor theorem), applied to the snake's window at
   n+2 with its lumped counts.
2. **Share identity.** `core_charge_sum_le 12 p`
   (`work/spectral/stronger/ShareBridge.lean`) gives
   `Σ_{k≤m} (24 coreAlpha p k + coreShare 12 p k) + 840 (m+1) ≤ 221136`.
3. **Combination.** Milestone 28's `combined_bound` (`lean/CombinedShareToy.lean`, core Lean,
   standard axioms) is proved for arbitrary sequences. From the telescoped inequality, the window
   bounds (each 5-window counted once, `window5`), `sym ≤ α`, `4 ≤ α 0`, `4 ≤ α m` and `1 ≤ α j`,
   it derives `(P + 4200 Q) m ≤ 1099800 Q + 7 P + R`. With `P/Q = 520`, `R = 2^10 - 1` this is
   `4720 m ≤ 1104463`, so **m ≤ 233**. The real chain needs one adapter: it replaces `rsum` by the
   project's `Finset.sum` over `Finset.range` (the form `core_charge_sum_le` uses), and identifies
   `sym (a j)` with `symC (coreAlpha p j)` as `upper_of_windows6` does.

So the k7 234 chain has one certificate type (`Refuted`) and an alpha aggregate. The 233 chain
needs:
- a second certificate type (`RefutedShare` with level `L`), with its own clause-soundness tags;
- a share table and `cover6S` in the automaton;
- a final combination step that uses the share identity `core_charge_sum_le` in place of
  `countSeq_facts`.

It needs no H9/F8 windows. The automaton stays k6: 34 · 6^5 states, 204 shards.

### 4. Modules and budget

- Automaton: Keys and Data modules, plus the share table (about 24 k 5-window fields, 5.7 k rows
  at most), 204 shards, Sequence.
  - The shards are the k6 shards with one more lookup: about 6 to 8 CPU-hours (5.9 measured for
    K235).
- Certificates: replays plus Cnf/Sat modules, one per paid certificate (see README for counts,
  hints, kernel hours and `.olean`).
- Glue:
  - `AllRefuted233` (merge of the plain chunks);
  - `AllShare233` (the share certificates by row, plus the floor theorems);
  - `UpperBound233` imports the chain, the glue and `ShareBridge`.

## Caveats

- Hints are measured for 1,130 (0.33 G) of the paid plain keys and modelled for the rest. The model is
  milestone 25's bins (measured/modelled 1.019 on 3,059 random keys there, and 1.00 on 14 here).
  The share costs rest on 27 replays (the fit's prediction/measured is 0.94). Share thresholds that
  were not re-solved are priced at the solve time of a higher level, which is an upper bound.
- Keys decided here (287 plain, 4,316 H8, share re-solves) are solver answers. Like every key
  beyond the 1,383 replayed ones, they still need their certificates.
- The greedy steps depend on order. A rerun with more measurements gives a slightly different set.
- Data from milestone 28 is read **as committed**: `git show HEAD:` on its `oracle_plain*` and
  `oracle_share*` files. The 232 refinement's newer exclusions (`oracle_plain_r232`,
  `oracle_share_r232`) were picked up from step 2′ on. Its context-share records
  (`ctxshare_r232`, 7-window thresholds) are a different certificate type and are not used.

## Files

| file | contents |
|---|---|
| `lib233.py` | paths, pools (committed milestone 28 data only), plain and share cost models, `best_pq`, `bound233`, cost summary units |
| `eng233.py` | `World`: the full product with share keys, BF, warm relaxation with undo, dual reverse-delete, exact drops and exact share lowering, save/load |
| `steps233.py` | `recost`, `prune`, `giants`, `exact`, `share` (re-solve at the used level), `h8` |
| `measure233.py`, `calib233.py` | replay costs of share thresholds and plain keys (FIFO, no proof on disk); the calibration (`data/calib233.json`) |
| `floors233.py`, `fam233.py`, `summary233.py` | step 8, step 9, the final summary |
| `data/keys233_best.json.gz` | **the best set**: `plain` [dirs, lumped syms, basis, hints], `share` [dirs, lumped syms, level used, proved lb, basis, hints], `h8` [dirs (reversed, uncounted last), syms, hints] |
| `data/cost233_best.json` | **cost summary**: hints, kernel-hours at 0.1 / 0.2 ms/hint, `.olean` GB at 2.5 B/hint, and the chain of steps |
| `data/set_*.json.gz`, `data/sum_*.json` | every intermediate set (`recost520`, `p520`, `g520`, `p520b`, `g520b`, `x520b`, `x519`, `p519`, `g519`, `p524`, `g524`, `h520`, `s520`) |
| `data/replay233.jsonl`, `data/oracle_plain233.jsonl`, `data/oracle_h8.jsonl`, `data/oracle_share233.jsonl`, `data/giants_*.json`, `data/h8log_h520.json`, `data/h8keys_*.json`, `data/floors_*.json`, `data/fam_*.json`, `data/cores233.jsonl.gz` | measurements, decisions and step logs |

Reproduce (about 3 h on one core):

```
python steps233.py prune 520/1/10 p520b
python steps233.py giants p520b g520b 3e8 1800
python steps233.py exact g520b x520b
python steps233.py h8 x520b h520 2700
python steps233.py share h520 s520 60 2400; cp data/h8keys_h520.json data/h8keys_s520.json
python floors233.py s520 20
python fam233.py s520 1800
python summary233.py s520 recost520 p520 g520 p520b g520b x520b x519 h520 s520
```
