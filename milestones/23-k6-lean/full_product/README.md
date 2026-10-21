# k6 plain key set on the full product (target 235)

Run of 21 October 2026, 19:35 to 21:00, on one core at `nice -n 19`, with solves one at a time,
next to two Lean builds. Everything here is solver-side. No certificate was replayed, and no Lean
module was generated or built.

## Answer

| | value |
|---|---|
| graph | the **full product** of the Lean k6 check: 34 shapes × 6^5 = 264,384 states, the same `shapes7`/`transitions` as `../scripts/gen_lean_automaton6.py` |
| λ = 4 with all known exclusions? | **yes, at once.** The 27,822 known lumped plain-UNSAT keys (k6_loop oracle, k6_w3, k6_w3_loop, radius-4 caches) give λ = 4 with potential range 4. No refinement round was needed (`rounds.jsonl`: round 0 is already done), and no 7-centre keys were used. The 31/8 cycle of `../data/k6A_full_product.json` is excluded by k6_w3/k6_w3_loop keys that the 3,103-key set lacked. |
| final key set | **`keys_235.json`: 1,287 keys** (4/43/212/986/42 with 2/3/4/5/6 counts) |
| of which already certified | **652** are in the replayed 236/237 sets (`direction_certificates_r4b/r4c.json`), cost 0 |
| new certificates | **635** (16 four-centre, 577 five-centre, 42 six-centre) |
| estimated LRAT hints of the new ones | **≈ 294 M** (largest single key 11 M) |
| estimated kernel time | **≈ 34 kernel-hours** at 0.42 ms per hint (the 237 rate), plus the 204 shards (≈ 7 CPU-h, milestone 23 README) |
| generator check | `gen_lean_automaton6.py --keys keys_235.json --lam 4/1 --provisional --dry-run`: **potential range 5 (3 bits)**, 13 BF rounds, Python re-check passed on 6,015,223 transitions, C = 29, **bound 235**. `--lam auto` gives minimum cycle mean exactly 4 (a 3-cycle with new counts 6,1,5). |

The Lean arithmetic: λ = 4/1 and 3 bits give 39 m + 6 ≤ 9171 + 28 + 7, i.e. m ≤ 235.
λ = 4 with range ≤ 7 is the same as "no walk of the full product has Σ(s − 4) < −7". The
Bellman-Ford potential started from 0 has the least possible range, so `fp.py` and `prune.py` test
exactly that.

## Method

1. **`fp.py`** loads every radius-4 plain status:
   - `k6loop.Plain`, which covers the milestone-10 caches, the share loop, s0_k6_ceiling and k6_loop;
   - `../../22-global-arguments/k6_w3/data/plain_k6w3.jsonl`;
   - `k6_w3_loop/data/plain_loop.jsonl.gz`;
   - this directory's `oracle_full.jsonl`.

   UNSAT keys with non-lumped ranges are expanded to the lumped keys they contain. Such a key, and
   any member of a k6_w3_loop range certificate, is UNSAT but needs its own certificate. The 3 kept
   keys of this kind were re-solved by `verify.py`: all UNSAT.

   `fp.py` builds the product from the generator's own functions, using canonical labels only. A
   label above max+1 gives the same transition. The generator itself, which enumerates all 9
   labels, confirmed the result.

   The loop mode (Bellman-Ford with predecessor chains, then testing the suffix windows of the
   violating walks, smallest first) exists but was not needed.

2. **`prune.py`** keeps every transition of the product with its exclusion count.
   - It first does a dual pruning: a weighted greedy hitting set of the critical transitions. This
     gains little here, because the least potential leaves 2.4 M critical transitions.
   - It then makes exact drops, most expensive first. A key is dropped when a warm-started
     Bellman-Ford still converges with min ≥ −7.
   - Finally it drops free keys, to shrink the tables.

3. **Giant replacement (`extend.py`).** The first pruning (`prune_p0.json`) still held two
   radius-4 four-centre keys:
   - `01203/(4,4,3,5)` and `01203/(3,5,4,3)`, cache solves of 46 s each;
   - the r4 fit estimates them at about 0.7 G hints each, ≈ 1.44 G hints together, about 170 kernel-hours.

   `extend.py` plain-tests all one-step extensions of every expensive key, on the left and right,
   one more direction and one more count. It ran in two rounds, at > 5 M and > 2.5 M estimated hints.
   - 793 tests, all UNSAT;
   - median solve time 0.15 s.

   Pruning again (`prune_p1`, then `prune_p2` with the calibrated costs) replaced both giants. That
   took the cost from 1.82 G to 0.29 G hints.

4. **Costs (`costs.json`).**
   - A key's cost is its measured hint count (`samples.jsonl`) where known.
   - For a cache key, it is the milestone-10 `est_hints_r4.jsonl` value.
   - Otherwise it is hints = 1.49e6 · t^0.843, where t is the key's own plain solve time.

   The fit uses 74 trimmed CaDiCaL LRAT samples: 45 new (`samples.py`, `sample_top.py`; proofs
   capped at 100 MB and deleted at once) and 29 from k6_loop. On all 74, the predicted sum is 0.96
   of the measured sum.

   The 10 most expensive kept keys were measured directly. They came out at 3.9–11.0 M hints, against
   estimates of 3.7–12.6 M.

   Cost of the final set by basis:

   | basis | keys | hints |
   |---|---|---|
   | measured | 42 | 75 M |
   | est_r4 | 214 | 77 M |
   | solve time | 379 | 142 M |
   | reused | 652 | 0 |

## Caveats

- The keys are solver answers (`--provisional`). Each new key still needs its LRAT certificate.
  CNFs have up to 4,040 variables, so they go through the O5k checkers.
- The cost assumes that the 652 reused keys' replay modules can be imported as they are. Counting
  them again would add their table estimates, ≈ 5.1 G hints, dominated by giants that were already
  replayed.
- The search for the cheapest set is greedy. A further `extend.py` round below 2.5 M would shave a
  few percent at most.

## Files

| file | contents |
|---|---|
| `keys_235.json` | the final 1,287 keys, `{"keys": [[dirs, alpha]]}`, which `gen_lean_automaton6.py --keys` consumes |
| `prune_p2.json` | its summary; `prune_p0.json` and `prune_p1.json` are the earlier passes (before the giant replacement, and with provisional costs) |
| `fp.py` | statuses, the full product, Bellman-Ford with chains, the refinement loop (`loop`, `eval`, `export`) |
| `prune.py`, `extend.py`, `verify.py` | cost-aware pruning, extension tests, own solves of derived keys |
| `samples.py`, `sample_top.py`, `samples.jsonl`, `costs.json` | LRAT calibration |
| `oracle_full.jsonl` | the 796 plain calls of this run (k6loop record format) |
| `rounds.jsonl` | the loop's round record (done at round 0) |

To reproduce:

```
nice -n 19 python prune.py p2 --reuse --drop-budget 1500
cd ../scripts && python gen_lean_automaton6.py --keys ../full_product/keys_235.json --tag T --lam 4/1 --provisional --dry-run
```
