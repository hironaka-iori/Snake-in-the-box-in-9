# A seven-centre (k7) automaton for 234: definition, full-product refinement, cost

Run of 25 October 2026, 18:18 to about 23:45: `nice -n 19` on one core, peak RSS under 0.6 GB,
next to the 235 Lean build. This is solver-side and Python-side only. No Lean module was written
or built. The 56 LRAT samples were written to scratch and deleted at once.

## Answer

| | value |
|---|---|
| automaton | **k7**: state = canonical 8-direction shape (132) × 6 lumped counts. The full product has **6,158,592** states; **3.13 M** of them are live under the closed-set rule below. Steps go to 505 induced 9-shapes. The k6 windows are unchanged, and two new window kinds are added: **F8** (8 directions, 7 counts) and **H9** (9 directions, 7 counts, the first centre uncounted). |
| bound | **(P + 35Q) m + 7Q ≤ 9171Q + 8P + 2^B − 1**. 234 needs 227P − 939Q ≥ 2^B and a potential range ≤ 2^B − 1. |
| chosen λ | **4516/1083 = 4.16990**, B = **13** (range allowed ≤ 8,191 = 7.56 count units). **Measured range on the full live product: 6,377** (5.89 units). Generator arithmetic: C = 8191 + 8·4516 − 7·1083 = 36,738, ⌊(9171·1083 + C)/(4516 + 35·1083)⌋ = **234**. |
| refinement | on the **full product the Lean check would enumerate** (all 132 × 6^6 states, dead states skipped by the closed-set rule). 54,338 H9 windows were decided at radius 4: **53,959 UNSAT**, 379 SAT, 1.8 h of solver time. No F8 window was needed. |
| key set `data/keys_l417d.json.gz` | **38,224 keys**: 1,383 k6 keys with certificates already replayed or being replayed (r4b, r4c, keys_235, cost 0), **19,553 more k6 keys** from the all-known pool, and **17,288 new H9 keys** |
| estimated LRAT hints | **34.3 G** = 28.8 G (k6 pool keys) + 5.5 G (H9) |
| estimated kernel time | **≈ 4,000 kernel-hours** of LRAT replay at 0.42 ms/hint (the 235 build is running at about 0.22 ms/hint, which would give ≈ 2,100 h), plus **≈ 55 CPU-hours** of shards |
| verdict | A k7 chain to 234 is **well defined and sound**, and the target holds on the full product. As pruned in 5.5 h it costs about **100×** the 235 chain. The cost is concentrated: 10 radius-4 giants hold 10.9 G, and 10,852 keys are costed at a class median (12.3 G, probably far too high). §4 lists the next cuts. **Disk is the hard blocker**: about 10 B of `.olean` per hint means about 340 GB at 34 G hints. |


## 1. The automaton

`k7.py` generalises `gen_lean_automaton6.py` (k6) by one step of memory.

| | k6 (milestone 23) | **k7 (this plan)** |
|---|---|---|
| state | 7-direction canonical shape, 5 lumped counts a(i+2..i+6) | **8-direction canonical shape d(i..i+7), 6 lumped counts a(i+2..i+7)** |
| shapes | 34 | **132** (induced 8-RGS) |
| full product | 34 · 6^5 = 264,384 | **132 · 6^6 = 6,158,592** |
| step | label d(i+7), count s = a(i+7) | **label d(i+8) < 9, count s = a(i+8)**; the step window X = state ++ [d] is an induced 9-RGS (**505** of them) |
| windows tested | 3..7 directions ending at the new vertex, 2..6 counts, both orientations | **(k6)** the same, unchanged; **(F8)** the 8-direction window d(i+1..i+8) with all 7 counts a(i+2..i+8), both orientations; **(H9)** the 9-direction window X with counts a(i+2..i+8), first interior vertex a(i+1) uncounted |
| potential row | (7-shape, t0), 6^4 fields | (8-shape, t0), **6^5 fields** of B bits |
| step inequality | P + pot(next) ≤ Q s + pot(cur) | the same |

**H9 keys and `Refuted`.** An H9 key is stored reversed, so that the uncounted vertex is the last
centre: the key `(canon(rev X), rev(a2..a8))` has 9 directions and 7 counts, and its certificate
is literally `Refuted (winOf ds) (boundsOf syms)`. `centresOf` takes `bounds.length` = 7 centres,
the first 7 of the 8 interior vertices, so the eighth is unconstrained. No change to
`LocalWindowModel`/`LocalWindowDirModel` is needed, and `AllRefutedList` applies as it is. The CNF
is the radius-4 model of `wincert.Encoding` with alpha = 7 bounds + `None`. CNFs have at most
4,513 variables (56 samples), so the O5k checkers (`--off 5000`) suffice.

**Closed set (sound, no enumeration).** A state whose *own* k6 windows (3..7 directions ending at
its last vertex, counts from its 6) are excluded never occurs in a snake: those windows are
windows of the snake, and the `Windows` premises already say that no snake window is excluded.
This includes the state at index 0. So the Lean check may skip such a state with no loss
(`own7 … || …` in `check7At` below). This costs nothing in the bound, and needs only that the step
lemma discharges `own7` from the premises `w2..w6` at the shifted index. The live states are
exactly the allowed k6 transitions: 3.0–3.5 M of the 6.16 M, depending on the k6 keys. The k7
product with this restriction is the line graph of the allowed k6 transitions, cut further by
F8/H9.

**Bound.** As `total_bound6`, with Ψ7(i) = pot(d(i..i+7), a(i+2..i+7)) and one more step of memory:

- telescoping from n = 0 to m − 8: `num·(m − 8) + Ψ7(m−8) ≤ den·Σ_{j=8}^{m−1} sym a_j + Ψ7(0)`;
- `sumA_ge7`: `7 + S7(m−8) ≤ sumA(m−1)`, since a1..a7 ≥ 1;
- so `num·m + 7 den ≤ den·sumA(m−1) + 8 num + (2^B − 1)` (`total_bound7`, needs m ≥ 8);
- with the aggregate `sumA(m−1) ≤ 9171 − 35 m`:

  **(P + 35 Q) m + 7 Q ≤ 9171 Q + 8 P + 2^B − 1.**

  This is the k6 formula with C = 2^B − 1 + 8P − 7Q in place of 2^B − 1 + 7P − 6Q, so the end
  term grows by P − Q.

**What 234 needs.** m = 235 is excluded iff 235(P + 35Q) + 7Q > 9171Q + 8P + 2^B − 1, that is

  **227 P − 939 Q ≥ 2^B**, with potential range ≤ 2^B − 1.

In count units the slack is σ = (2^B − 1)/Q < 227λ − 939, so λ > 939/227 = 4.1366. `best_pq`
picks Q ≤ 2000 that maximises σ:

| λ ≈ | P/Q | B | slack σ (count units) |
|---|---|---|---|
| 4.15 | 5590/1347 | 12 | 3.04 |
| 4.16 | 6423/1544 | 13 | 5.31 |
| **4.17** | **4516/1083** | **13** | **7.56** |
| 4.18 | 6968/1667 | 14 | 9.83 |
| 4.20 | 4788/1140 | 14 | 14.37 |

For comparison, milestone 24's 79/19 with range 106 fails this test (only 63 is allowed), and
167/40 with range 216 passes (255 is allowed). Condition for the Lean check: no walk of the full
(live) product has Σ(P − Q s) > 2^B − 1. Bellman-Ford from 0 gives the least range, so the
generator test is the same as in `fp.py`.

## 2. Refinement on the full product (`k7.py loop`)

`K7` builds the product exactly as the Lean check enumerates it:

- the 132 canonical 8-shapes, i.e. the k6 extensions `fp.Product.ext`;
- every induced 9-RGS X = shape ++ [label], with a label of at most max + 1. Labels above max + 1
  give the same transition; the Lean shards should enumerate only canonical labels (§5);
- an allowed mask over the 6^7 counts (a2..a8) for each X:
  `alive[source] ∧ alive[target] ∧ no F8/H9 key`, where alive[·] is the k6 own-window test (k6
  key counts `fp.Product.CNT`).

Bellman-Ford (Gauss-Seidel, dirty shapes only, about 1 s a round) runs with weights Qs − P from
0. Its predecessor walks to the nodes below −L, or below −L/2 in the cycle regime, are cut by
the H9 window of each transition, most frequent first, up to 1,500 a round.

| run | k6 base | λ | result |
|---|---|---|---|
| loop 1 | all 28,618 known keys | 4.15 (slack 3.04) | stopped. The *fringe* (transient walks of 13–17 steps with low counts, 136k nodes below −L after 4 rounds) needs thousands of cuts a round, and the minimum did not move |
| loops 3–4 | all known | **4.16990** | **converged after 31 BF rounds: range 5,520 ≤ 8,191**, with 17,942 H9 keys |
| loop 4 | all known | 4.17996 | stopped after one round, at 466 BF rounds per round (near the cycle mean) |
| loop 5 | the 1,383 free keys only | 4.16 | stopped: the fringe of the free base stays at −9.6 units after 20k cuts |

98–100 % of the H9 windows met on bad walks are UNSAT, as in milestone 24 (24,757 of 25,281).

## 3. Cost-aware pruning (`prune7.py`, `replace7.py`, `lrat_samples.py`)

**Costs.**

- k6 keys: `full_product/prune.py load_costs`. The keys of r4b, r4c and keys_235 count as free.
- H9 keys: binned on their own solve time from **56 LRAT samples** (`data/lrat_samples.jsonl`;
  CaDiCaL `--lrat`, hints of the empty clause's cone; every proof was deleted at once):

  | solve time | < 0.03 s | 0.03–0.04 | 0.04–0.06 | 0.06–0.1 | ≥ 0.1 s |
  |---|---|---|---|---|---|
  | mean hints | 1.9 k | 13.8 k | 19.9 k | 107 k | fit 1.49e6·t^0.843 (0.6–1.3× on 7 samples) |

  Most H9 windows are nearly trivial: the median sample is 1.6 k hints. The k6 power fit
  overestimates them 10–100×. Samples have at most 4,513 variables and 82,596 clauses, with
  0.2–3.5 MB of LRAT.

**Dual reverse-delete (`prune7.py`).**

- Take the Bellman-Ford potential of the current set. A dead state gets the value it would have
  if revived: the minimum over its in-transitions, clipped to [−L, 0].
- A transition is critical when its reduced cost is negative. A k6 key covers, in k7, every
  transition whose *target* or *source* state it kills. Coverage counts are per transition, with
  their multiplicity.
- Keys are visited by decreasing cost and dropped while every critical transition stays
  covered.
- The potential stays valid, so the bound holds by construction. The final set is re-checked by
  a fresh BF on the full product.

**Replacement (`replace7.py`, the k7 analogue of `extend.py`).** A kept k6 key is needed only for
the critical transitions it alone covers, median 22. Their H9 windows are decided. If all are
UNSAT and cost less than the key, the key goes:

- pass 1, by cost per cut: 790 keys replaced (7.4 G gross);
- pass 2, giants first, with the cost test: 901 of 1,210 replaced (2.0 G gross).

| set | k6 paid | H9 | hints |
|---|---|---|---|
| pruned, all-known pool (`prune_l417b`) | 21,260 | 6,019 | 38.6 G |
| + replacement 1 (`prune_l417c`) | 20,482 | 11,295 | 35.5 G |
| **+ replacement 2 (`prune_l417d`, final)** | **19,553** | **17,288** | **34.3 G** |

**What the 34.3 G consists of (`data/l417d_breakdown.json`).**

| basis | keys | hints |
|---|---|---|
| reused (certified 236/237/235) | 1,383 | 0 |
| k6, milestone-10 r4 estimates | 448 | 11.4 G (**10 giants: 10.9 G**; each has > 6,000 uniquely covered critical transitions) |
| k6, own solve time | 8,252 | 5.1 G |
| k6, no own solve (class median 1.13 M) | 10,852 | 12.3 G (an upper guess) |
| H9 | 17,288 | 5.5 G (median 13.8 k) |

## 4. Next cuts (not done here)

1. **Giants:** `extend.py`-style one-step extensions of the 10 giants. In milestone 23 this
   took 1.44 G to near 0 with 793 cheap solves. It is worth up to about 10 G.
2. **Median-costed keys:** solve them (0.1–1 s each) and cost them on their own time. Many are
   range-certificate members. Then replace them by H9 where cheaper. At H9-like proof sizes this
   is worth up to about 10 G.
3. **λ choice:** only 4.17 was completed. 4.18 (slack 9.8) and 4.165 were not tried with
   pruning. The fringe argues for λ ≥ 4.17. The cycle family argues against > 4.18.
4. **F8 generalisation** of kept H9 keys: none was tried.

A plausible target after steps 1–2 is 10–15 G hints, that is 1,200–1,800 kernel-hours at
0.42 ms, or 600–900 at the observed 0.22 ms.

## 5. Lean plan

**Core module `WindowAutomaton7Defs.lean`** (a copy of `WindowAutomaton6Defs` with one more
step):

- `Tables7`: the same fields as `Tables6`. Exclusion rows are keyed by (window shape code, first
  count). An 8-direction F8 row and a 9-direction H9 row carry `symIdx` masks of 7^6 bits.
- `pot7 T h t`: the row is (8-shape code, t0) and the field is `cntIdx` of t1..t5 (6^5 fields of
  B = 13 bits, about 12.6 kB a row, 792 rows).
- `wforbH T ds syms := wforbA6 T ds.reverse syms.reverse`: one orientation only, the reversed
  key form.
- `own7 T c t0..t5` := the five k6 lookups of `c.take 8` ending at its last vertex (counts
  t4..t5 up to t0..t5).
- `check7At T c t0` (c has 9 directions):
  `!inducedPattern c || allSym t1..t5 (own7 … || allSym s (wforb6 (c.drop 6) [t5,s] || … || wforb6 (c.drop 2) [t1..t5,s] || wforb6 (c.drop 1) [t0..t5,s] || wforbH T c [t0..t5,s] || decide (num + pot7 (c.drop 1) [t1..t5,s] ≤ den·s + pot7 (c.take 8) [t0..t5])))`.
  The `(c.drop 1)` lookup with 7 counts is F8. Lookups with 3..7 directions are the k6 table.
- `StepOK7`: ∀ c of length 9 with `isRGS c 0`, ∀ t0 ∈ 1..6, `check7At`.
- `ShardsOK7` uses the RGS labels `rgsBound h 0` instead of `allBelow 9`. This saves the
  non-canonical labels, and `StepOK` only quantifies over RGS. Together with a
  `ShapesCover8` (`allRGS 9`, split by prefixes of length 5) it gives `check7_of_shards`.
- `step7_raw` / `step7`: `own7` is rewritten to `false` from the premises `w2..w6` at index i
  (the state's own windows), as `hw2..hw6` are used now.
- `Windows7`: `w2..w6` of `Windows6`, plus `w7` (8 directions, 7 counts) and
  `wh : ∀ j, j + 9 ≤ m → wforbH T [d j..d (j+8)] [a (j+2)..a (j+8)] = false`.
- `invariant7` (n + 8 ≤ m), `sumA_ge7` (7 + S7 n ≤ sumA (n+7)) and
  **`total_bound7`: `num·m + 7 den ≤ den·sumA (m−1) + 8 num + (2^bits − 1)`** for m ≥ 8.

**Bridge `DirectionWindowBridge7.lean`:**

- `keysOK7`: a key has `syms.length + 1 = ds.length` for 3 ≤ |ds| ≤ 8, or |ds| = 9 and
  |syms| = 7. `symIdx_inj` applies per length.
- `Cover7` row by row (`cover6_rows` unchanged; about 15k nonzero rows).
- `window_refute7` / `no_forb_window7` for lengths 3..8 are the k6 proofs with one more length.
- `no_forb_H9` is new. A snake window d(j..j+8), reversed, satisfies `Axioms` for
  `centresOf (winOf ds) (boundsOf syms)` with 7 bounds: the eighth centre carries no constraint.
  The proof is the same relabelling/reversal argument (`refuted_dir`). `centresOf` already takes
  `bounds.length` centres.

**`AggregateDirection7Conditional.lean`:** `upper_of_refuted7` gives
`(num + 35 den) m + 7 den ≤ 9171 den + 8 num + (2^bits − 1)`. With 4516/1083 and 13 bits this
is `42421 m + 7581 ≤ 9976512`, so **m ≤ 234**: m = 235 gives 9,976,516, a margin of 4.

**Generator `gen_lean_automaton7.py`** (to write from `gen_lean_automaton6.py` + `k7.py`):

- `--keys` takes the three key kinds of `keys_l417d.json.gz`.
- It runs BF on the full product, with the closed-set skip, at `--lam 4516/1083`.
- It re-checks in Python against the decoded tables, as now.
- Modules: Keys (chunks of 400), Data, **792 shard files** (8-shape × t0), each holding one
  `decide +kernel` per (canonical induced label, t1). That is **18,180 declarations of at most
  7,776 transitions**, the size of a k6 per-label declaration (≈ 2.0 GB, 13 s), with
  `Elab.async false`. Then Sequence.
- Shard cost: 71.7 M live evaluations (505 X × live sources × 6) against 10.4 M in the k6
  shards (5.9 CPU-h measured, 2.0 ms each), times about 1.3 for the extra lookups:
  **≈ 55 CPU-hours**.

**Certificates:**

- 36,841 new LRAT replays: `gen_lean_lrat_o5k.py --off 5000`, since every CNF is ≤ 4,513
  variables; Cnf/Sat/replay modules as in `certify/replay_k6.py`.
- H9 keys use the same `winOf`/`boundsOf` statement, with 7 bounds.
- The 19,553 extra k6 keys need their cores (`gen_lean_core`), like the 635 of K235.

**Glue:**

- `AllRefuted7 = merge(allRefuted237, allRefuted236, AllRefuted6K235, AllRefutedK7a [k6 pool], AllRefutedK7h [H9])`
  via `allRefuted_of_merge` (`LocalWindowDirGlue6`), one kernel merge of the tags.
- `UpperBound234` imports the replays, the K7 chain and the glue, as `UpperBound235`.

**Resources (blocking).** The replay oleans take 8.5–11.5 B per hint (certify/README), so
34 G hints need about **340 GB**. Even after the cuts of §4 that is 100–150 GB, against 0.7 GB
free now. The 234 chain therefore needs either a larger disk or a replay mode that checks and
discards (one `lean` run per key with no `.olean` kept, plus an external axiom-free audit of the
results). Do not start it on this machine.

## Caveats

- The H9 decisions are uncertified CaDiCaL answers (56 sampled ones have LRAT). The k6 pool keys
  are the known plain-UNSAT solver answers.
- Costs: H9 is calibrated on 56 samples. 10,852 k6 keys carry a class-median guess.
- One λ only (4.16990). The search is greedy and stopped at the time cap.
- No Lean was written or run. The shard estimate extrapolates the K235 shard times.

## Files

| file | contents |
|---|---|
| `k7.py` | the k7 product (`K7`: shapes, 9-shapes, masks, closed-set live states), structured Bellman-Ford with predecessors, H9/F8 key forms, the oracle (`data/oracle_k7.jsonl.gz`, 54,338 decisions), `best_pq`, `bound`, the refinement `loop` (`--base all|free`) |
| `prune7.py` | costs, revived-state potential, critical transitions, coverage counts, reverse-delete, final full-product re-check → `data/keys_<tag>.json.gz`, `data/prune_<tag>.json` |
| `replace7.py` | k6 → H9 replacement → `data/replace_*.json` |
| `lrat_samples.py` → `data/lrat_samples.jsonl` | the 56 LRAT hint counts |
| `data/keys_l417d.json.gz` | **the key set**: `keys` = `["k6", dirs, syms]` / `["H", dirs, syms]` (H9 in reversed, uncounted-last form), `cost`, `summary` |
| `data/l417d_breakdown.json` | cost by basis, live states, live (X, source) pairs |
| `data/loop_rounds.jsonl` | the rounds of the λ = 4.16990 loop |

Reproduce: `nice -n 19 python prune7.py 4.17 T --start l417c` (or without `--start`, from the full
pool), then `python replace7.py 4.17 T 1.0 [--giants]`.

