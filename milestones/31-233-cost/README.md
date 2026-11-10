# The certificate cost of a Lean-checked 233 (share-weighted k6 chain)

Run of 9–10 November 2026, about 20:10 to 03:00. It used one core at `nice -n 10` (peak RSS about
0.4 GB) and added under 2 MB of data. Solver and Python only: no lake and no Lean. Every LRAT proof
streamed through a FIFO into `lrattrim` and was never stored. The container restarted once (22:15);
the run resumed from the committed state.

**Answer.** Milestone 28's 233 route is the share-weighted k6 chain at λ = 520, i.e. 13/3 in alpha
units. After the cost reduction below it needs

> **@@HINTS@@ G LRAT hints in @@NCERT@@ certificates**: @@PLAIN@@ plain keys (including @@H8@@ H8 cuts)
> and @@SHARE@@ share thresholds, on top of the 1,383 replayed keys and main's share floors.
> At checker v3's 0.1 ms/hint that is **@@KH1@@ kernel-hours** (@@KH2@@ at 0.2 ms/hint), and about
> **@@GB@@ GB of `.olean`** at 2.5 B/hint, plus about @@CNF@@ GB of Cnf/Sat modules.
> @@FAMLINE@@

That is about **2.2×** the k7 234 set (1.73 G; 1.49 G with L1/L2), for one more edge. The first
estimate of milestone 28 was 47 G, so the reduction is about **@@FACTOR@@×**. The set is
`data/keys233_best.json.gz` and the summary is `data/cost233_best.json`.

## The bound being certified

With weight `w = Q (120 s + L(k5)) − P` on the allowed transitions of the Lean k6 full product, and
a Bellman-Ford potential of range at most `2^B − 1`, milestone 28's (*) gives
`(P + 4200 Q) m ≤ 1099800 Q + 7 P + 2^B − 1`. Here:

- `s` is the new lumped count;
- `L(k5)` is the certified share level of the trailing 5-window.

So m = 234 is excluded iff `227 P − 117000 Q ≥ 2^B` (`lib233.best_pq`, `bound233`). At P/Q = 520/1
with B = 10: `4720 m ≤ 1104463`, so **m ≤ 233**. The range allowed is 1,023; the best set uses
@@RANGE@@. Every set below was re-checked by a fresh Bellman-Ford on all 6,158,592 transitions.

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
| 7. share thresholds re-solved at the level used | `s520` | 520 | | @@S7SHARE@@ | @@S7HINTS@@ | @@S7SAVED@@ |
| 8. main's Lean share floors | | | | | | @@FLOORS@@ |
| 9. families L1/L2 | | | | | | @@FAM@@ |

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

@@BEST@@

## Lean plan for the share-weighted chain

@@LEANPLAN@@

## Caveats

- Hints are measured for @@MEAS@@ of the paid plain keys and modelled for the rest. The model is
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
| `data/replay233.jsonl`, `data/oracle_plain233.jsonl`, `data/oracle_h8.jsonl`, `data/oracle_share233.jsonl`, `data/giants_*.json`, `data/h8log_h520.json`, `data/h8keys_*.json`, `data/floors_*.json`, `data/fam_*.json`, `data/cores233.jsonl` | measurements, decisions and step logs |

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
