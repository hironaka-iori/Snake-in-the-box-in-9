# Realizability of the critical shape cycles

Run of 25 October 2026, at most 2 cores at `nice -n 10`, peak RSS 2.8 GB. This is solver-side and
Python/C-side only. No Lean module was written or built, and no SAT certificate was produced.

## Question

The direction automata remember only the **shape** of the last 7 directions: the
restricted-growth relabelling `canon` of `gen_lean_automaton5/6.py`. A real snake uses 9
concrete coordinates. Lift each critical cycle of shapes to concrete labels, and find the
longest unrolling that is still an induced path of Q9. If it is short, forbid the long shape
pattern (a finite check, with no LRAT) and recompute the minimum cycle mean.

## What a cyclic shape walk allows (`shapes.py`)

A state's direction part is `canon(x[t-6..t])`. The transition with label `d` moves to
`canon(window[1:] + (d,))`. Along a fixed walk of shapes, each step is therefore one of two kinds.

- **Repeat.** The new label is one of the labels at window positions 1..6. Then the new
  direction is forced: it equals `x[t-δ]` for a δ in 1..6.
- **Fresh.** The new label is a new RGS symbol. Then the new direction is any coordinate that is
  not among the last 6 directions. It may equal the direction 7 steps back: the automaton has two
  parallel edges here (label `c[0]` and label max+1), and they carry identical windows.

Without loss of generality the first 7 directions are the start shape itself, since any
coordinate permutation preserves the problem. Labels never used so far are interchangeable,
so only the smallest of them is tried at a fresh step.

**L_max(phase)** is the largest n such that some induced path with 7 + n edges has its
consecutive 7-windows equal to `states[phase], …, states[phase+n]`. The induced condition is
that every segment of 2 or more steps has XOR weight at least 2.

How it is computed:

- `unroll.c` runs an exhaustive DFS.
- `brute.py` is an independent check in pure Python: no symmetry reduction, all 9 labels, and
  `canon` tested directly. It agrees on every cycle that the DFS settles in at most 200k nodes.
- Every witness is re-checked by `shapes.check_sequence`.

## 1. L_max of the saved critical cycles (`collect.py`, `lmax.py`; `data/cycles.json`, `data/lmax.json`)

| cycle | shape period | rules (0 = fresh, δ = repeat) | L_max by phase | L_max |
|---|---|---|---|---|
| **k6 keys_235, λ = 4 critical 3-cycle** (counts 6,1,5) | 3 | 5,0,3 | 15,16,15 | **16 steps = 5.3 periods** (path of 23 edges) |
| k6A 31/8 8-cycle (3,103-key set) | 4 | 5,4,4,0 | 19,18,17,17 | **19 = 4.75 periods** |
| k6_w3 next binding period-6 cycle (226.1) | 6 | 4,0,3,5,0,4 | 21,22,… | **22 = 3.7 periods** |
| s0_k6_ceiling rigorous 14-cycle (222.6) | 14 | 6,4,4,0,3,5,0,4,4,0,3,6,3,0 | 1..11 | **11 < 1 period** |
| **237 automaton (r4b) own minimum cycle**, recomputed | 14 | 6,6,4,4,0,5,4,4,0,5,3,5,0,3 | 2,1,14,…,3 | **14 = exactly 1 period** |
| **236 automaton (r4c) own minimum cycle**, recomputed | 11 | 5,3,6,6,4,4,0,3,6,4,0 | 3,2,1,1,10,…,4 | **10 < 1 period** |
| k5 share-loop period-3 ceiling (μ = 4.7194; same shape cycle as the w3_survey 8497/6 ceiling) | 3 | 4,4,0 | 91,93,92 | **93 = 31 periods** (exact; 3.8 M DFS nodes) |
| **k6 all-known 4.0625 walk** (= the plain-A 65/16 cycle; shape period 8) | 8 | 4,4,0,0,3,5,0,0 | ≥ 85,84,84,88,… | **≥ 90 = 11.25 periods** (no exhaustive answer: 10^10 DFS nodes, `data/deep_dfs.json`) |
| constant shape 0123456 (any 7 consecutive directions distinct) | 1 | 0 | — | **≥ 114** (10^10 nodes) |

So the cycles fall into two groups.

- **Short.** The λ = 4 3-cycle of keys_235, the 31/8 cycle, the w3 cycles, and the 236/237
  minimum cycles cannot be followed for long. The 236/237 cycles cannot even be followed for
  one full period. Each of these is a cheap "long window" exclusion on shapes alone, a decide
  over at most about 1,000 label choices.
- **Long.** The all-distinct-shape walks and the share-type cycles are realizable for 90–114+
  transitions. That is half of a snake.

## 2. Forbidding the patterns (`cutloop.py`, `cut3.py`)

**The run-tracking product.** A DFA state is the set of active runs (cycle, start phase,
length). A shape transition extends a run, opens one, or kills the walk once a run exceeds
L_max(start phase). Opening a run is skipped when an earlier run already sits at the same
position: an earlier start dominates, because every suffix of a realizable run is realizable.

**Computing the mean.** On the product of the full k6 graph and this DFA:

- the exact minimum cycle mean is found by a Lawler descent (Bellman-Ford predecessor cycles,
  then an exact BF at the cycle mean);
- the bound uses the k6 Lean arithmetic (`(P+35Q)m + 6Q ≤ 9171Q + 7P + 2^bits − 1`).

### keys_235 (1,287 keys)

- **The 3-cycle is not the only λ = 4 cycle.** Cutting it exactly (runs ≤ 16; `data/cut3_keys235.json`):
  - the product grows from 264,384 to 622,080 states (113k live, 1.61 M live transitions);
  - λ stays **4**, so the bound stays **235**.
  - The next critical cycle is a 4-cycle on the constant shape **0123456** with counts 2,5,5,4.
    Its L_max is ≥ 114.
- **Cutting that one too, optimistically** at the DFS lower bound of 105 (`cutloop_keys235_opt.json`):
  - the product has 1.08 M states and 5.66 M live transitions;
  - λ is still **4**, now on a 20-cycle that mixes 0123456 with 0123450.
- **Why the loop cannot end.** The critical subgraph is huge: with the optimal potential (range
  5), **583,909 of the 984,454 live transitions have reduced cost 0**. `critical.py` finds a
  **realizable** walk in that subgraph of **125 transitions**:
  - it is an explicit induced path of **132 edges**, with a valid count lift;
  - its count sum is 498, a mean of **3.984**;
  - the data are in `data/critical_walk_keys235.json`.

  Shape cuts are sound, so they can never remove it.

### All 28,618 known plain-UNSAT keys (plain ceiling 4.0625, m ≤ 235.35)

- The binding walk has λ = 65/16 and shape period 16. It is built from two shape loops,
  A = 0123014·0123045·0123452·0123412 and an 8-block B, with L_max ≥ 84–88.
- **Cutting it optimistically** at its DFS lower bounds (`cutloop_allknown_opt.json`):
  - the product grows **×40**, to 10.6 M states and 16.1 M live transitions, at 2.8 GB;
  - λ stays **65/16**, now on an 80-cycle that strings A and B blocks together in another order
    with the same counts.
- Every word in {A, B}* carries mean 65/16, and single words stay realizable for 84+ steps. So
  per-cycle cuts are evaded by re-ordering, and a second round would pass the 4 GB cap. This
  run was stopped there.

## Verdict

1. **The idea is correct and cheap per cycle.** Several critical cycles are genuinely
   unrealizable after a few periods, or even within one period:
   - λ = 4 of keys_235: 16 steps;
   - 31/8: 19 steps;
   - the 236 and 237 automata's own minimum cycles: under one period.

   The exclusion needs no SAT certificate. It is a finite check: ≤ 1,136 brute-force nodes for
   the 3-cycle, a Lean `decide` over ≤ 30-vertex paths.
2. **It does not lower the bound.**
   - keys_235 stays at **235** (λ = 4). All-known stays at **4.0625 / 235.35**.
   - In both sets the minimum mean is carried by a large critical family, not by one cycle.
     That family contains walks that are realizable for 90–125+ transitions:
     - the all-distinct shape 0123456 for keys_235;
     - the A/B block family of the 65/16 walk for all-known.
   - No sound shape cut shorter than about 100 directions touches these walks. Cutting one
     periodic word only moves the minimum to a re-ordered word with the same mean.
   - Reaching 234 needs λ ≳ 4.15. Over realizable stretches of 100+ steps, that would require a
     potential range of order 15+ α units and runs of 100+ directions tracked in the state. That
     amounts to a much longer direction memory, not a pattern cut.
3. **Cost and Lean.**
   - A single short-cycle cut is about ×2.4 in states (3-cycle: 264k → 622k) and adds no LRAT.
   - It needs a new framework, though: a run counter in the Lean state, plus a bridge lemma
     that a snake's shape sequence avoids the pattern.
   - A long-cycle cut costs ×4 (keys_235) to ×40 (all-known) per pattern, and gains nothing.

**Next critical cycle after the cuts:**

- keys_235: a 4-cycle on 0123456 with counts 2,5,5,4, then a 20-cycle on 0123456/0123450, at λ = 4;
- all-known: an 80-cycle of A/B blocks at 65/16.

## Files

| file | contents |
|---|---|
| `shapes.py` | `canon`, the transition rule (repeat δ or fresh), `unroll` (calls `unroll`), independent witness check |
| `unroll.c` | exhaustive DFS for L_max (`gcc -O2 -o unroll unroll.c`) |
| `brute.py` | pure-Python cross-check without symmetry reduction |
| `sat_lmax.py` | SAT encoding (pysat/CaDiCaL) of "n steps realizable". Not needed in the end: the instances at n ≈ 110 did not finish in 5 min |
| `collect.py` → `data/cycles.json` | the cycles. Some are reconstructed from window keys; the 236/237 ones are recomputed with `refine.Automaton(7,5,5)` and Howard |
| `lmax.py` → `data/lmax.json` | L_max per phase, with witnesses. `data/deep_dfs.json` holds the 10^10-node runs |
| `cutloop.py` → `data/cutloop_*.json` | the run-tracking product and the exact minimum-cycle-mean loop (`keys235` / `allknown`, `optimistic` mode = cut at DFS lower bounds, a ceiling only) |
| `cut3.py` → `data/cut3_keys235.json` | the exact cut of the λ = 4 3-cycle alone |
| `critical.py` → `data/critical_walk_*.json` | long realizable walks in the zero-reduced-cost subgraph (randomised DFS, re-checked) |

## Counts along realizable walks

Second run of 25 October 2026: `nice -n 19` on one core, peak RSS 0.93 GB. Solver-side only.
No Lean module was written or built, and no new certificate was produced (only 6 sample LRATs,
in scratch).

### Question

Sections 1–2 lifted the critical walks to concrete directions but ignored the counts. The
automaton's counts are only checked by windows of at most 6 counted centres and 7 directions.
Is a long realizable walk still realizable once its counts are imposed along the concrete path?

### Model (`counts_sat.py`)

- One variable per vertex of the **whole** Q9. The clauses are those of `wincert.Encoding` with
  the ball equal to Q9: degree ≤ 2, at most 2 endpoints, no 4-cycle, the 6-cycle rule, and the
  path selected. There are cycle cuts until no extra cycle remains.
- The count of transition t belongs to vertex `vs[7+t]`, the centre between the last shape
  direction and the new one (`fp.windows`). The lumped count s means α = s for s ≤ 5 and
  α ∈ [6, 21] for s = 6.
- SAT is a real snake of Q9 through the segment with those counts. As a sanity check, a
  20-centre stretch of the 191-edge snake from `12-construction-196` is SAT with its own counts.
- Three conditions are tested:
  - **exact**: every vertex has the walk's lumped count;
  - **mean**: every prefix has Σ min(α, 6) ≤ λ(t+1) + R, with R = potential range / Q. This holds
    for every count lift of a walk in the critical subgraph;
  - **minsum**: the exact minimum of Σ min(α, 6) over a window, by totalizers and a descending
    bound.
- `dfs` explores **every** concrete labelling of the shape walk. The first 7 directions are the
  start shape, and unused labels are interchangeable. Each prefix is pruned by the exact or the
  mean condition.

### 1. The critical walks die within a few steps (`data/counts_report.json`)

| walk (milestone 24) | steps | count mean | concrete labels, exact: longest SAT | all labels, exact | all labels, mean ≤ λ + R | min lumped mean on the concrete path, 20 / full |
|---|---|---|---|---|---|---|
| keys_235 λ = 4 walk (`critical.py`) | 125 | 3.984 | 1 | 1 | 6 | 5.90 / 6.00 (walk: 3.90 / 4.01) |
| all-known 65/16 walk (`critical.py`) | 76 | 4.079 | 5 | 5 | 7 | 5.70 / 6.00 (walk: 4.00 / 4.09) |
| all-known 16-cycle (A/B blocks), phase 0 | 160 | 4.0625 | — | 3 | 7 | — |
| all-known 80-cycle (cutloop round 1), phase 0 | 160 | 4.0625 | — | 4 | ≥ 8 (DFS capped at 150 s) | — |
| keys_235 4-cycle on 0123456 (2,5,5,4) | 160 | 4.0 | — | 3 | ≥ 6 (capped) | — |

"Longest SAT" is the number of transitions whose counts can be imposed. The "all labels"
columns are exhaustive DFS answers unless marked capped. The last column gives the exact
minimum of Σ min(α, 6) per centre over the first 20 centres, and over the whole path, against
the walk's own count mean on the same centres.

So, once counts are imposed, **no walk survives more than 5 steps with its own counts, or
about 6–8 steps under the weaker mean condition**, under any labelling. Along the
concrete witness paths of milestone 24, the true lumped mean is about **6.0**, against the
walk's 3.98–4.08. Those paths are loose: a vertex gets α ≤ 5 only where the path folds back
within distance 2 of itself, so most centres have α ≥ 6.

The minimal UNSAT windows along the 4.08 walk (radius 4, own directions only) have **7–8
counted centres** (8–9 directions). There are 61 of them at 76 end positions, plus 8 with 5–6
centres. That is just past the automaton's memory. These are "long windows" in the sense of the
question, but short ones: 8–10 directions, not 30–40.

### 2. Long-window refinement of the all-known k6 product (`ctxcut.py`, `ctxcut2.py`)

**Stage 1: 8-direction windows (`ctxcut.py`, `data/ctxcut_allknown_R0.json`).** A k6
transition already knows 8 directions d0..d7 and 6 counts (w2..w7). The window is decided at
radius 4, and the transition is removed if UNSAT. The loop is lazy and touches only the
critical subgraph.

- λ goes from 65/16 to **57/14** after 56 removals, then stalls.
- The stalling 14-cycle (counts 6,3,3,6,4,3,6,3,2,6,4,6,2,3) has only SAT 8-direction windows.

**Stage 2: 9-direction windows with 7 counts (`ctxcut2.py`, `data/ctxcut2_allknown_R0.json`).**
This works on the line graph: 541,091 live k6 transitions and 7,581,442 consecutive pairs. That
is the k7 automaton restricted to live k6 states. A pair is removed only if every concrete
version of its window is UNSAT; a fresh label may be d0 or a new coordinate.

| round | λ | pot. range | bound (k6 formula) | conservative bound (+P end term) | UNSAT windows so far |
|---|---|---|---|---|---|
| 0 | 57/14 = 4.071 | 67 | 235 | 235 | 11 |
| 10 | 33/8 = 4.125 | 43 | 235 | 235 | 2,618 |
| 16 | 83/20 = 4.150 | 107 | 235 | 235 | 4,390 |
| **20** | **79/19 = 4.158** | 106 | **234** | 235 | **5,626** |
| 23 | 25/6 = 4.167 | 32 | 235 (one bit of range too many) | 235 | 10,583 |
| **26** | **167/40 = 4.175** | 216 | 234 | **234** | **10,909** |
| 35 | 67/16 = 4.1875 | 88 | 234 | 234 | 12,963 |
| 42 (stopped at the cap) | **21/5 = 4.2** | 28 | 234 | 234 | 24,757 |

- In 42 rounds, λ never stalls at 9 directions. Each round removes 20–9,425 pairs.
- Up to round 19, the critical cycles have mean (4k+1)/k. The binding family thins out one cycle
  length at a time.
- At λ = 25/6 and 21/5 the critical family is large: 4,161 and 9,653 pairs. The run stopped
  at its 1.5 h cap, with the last critical cycle being a 5-cycle with counts 4,4,6,2,5.
- 233 would need λ ≳ 4.47, out of reach at this window length.

### 3. Cost

- **Keys.** 234 needs about **5.6k** (k6 arithmetic) to **11k** (conservative end term) new
  9-direction keys with 7 counts, and 21/5 needs about 25k. These are upper estimates from a
  lazy loop without key minimisation; wildcarding counts would merge many keys. The all-known
  set has 28,618 keys.
- **LRAT** (`longwin.py`, `data/longwin_allknown.json`, 6 samples): radius 4, about 75–80k
  clauses and 4.3–4.7k variables. DRUP has 30–45k lines; LRAT is **0.44–1.8 MB** per key, mean
  about 0.8 MB.
  - 11k keys come to about **9 GB** of raw LRAT; 25k keys to about 20 GB.
  - drat-trim verified all 6 samples.
- **Automaton.** The state must remember 8 directions and 6 counts (k7).
  - The full product is 132 × 6^6 = **6.16 M states**, 23 times the k6 product.
  - Only 541k of them are live. Using that needs a closed-set argument in Lean, or 23 times the
    k6 kernel enumeration.
  - The bridge needs one more window length (8–9 directions) in `check6At`.
- **Margin.** The k6 end terms (`(P+35Q)m + 6Q ≤ 9171Q + 7P + 2^bits − 1`) must be redone for
  one more step of memory. The column "+P" assumes one more count in the end term.
  - Potential range matters too: at λ = 25/6 a range of 32 instead of ≤ 31 costs the 234.
  - A range-minimising potential (not attempted) would help.

### Verdict

- **The critical walks of milestone 24 are not real.** They were realizable for directions only.
  With counts, every labelling fails within 1–5 steps (exact) or about 6–8 steps (mean
  condition).
- **Long windows do cut below λ = 4, and above 4.15.** The exclusions needed are only 8–9
  directions long, and the λ climb did not stall in 42 rounds.
- **This is a route to 234, not below it.** The cost is:
  - a k7 automaton: 6.2 M states for the full product, or 541k live with a closed-set argument;
  - about 6–11k new radius-4 keys: about 5–9 GB of LRAT before minimisation;
  - a re-derived end-term inequality.
- **Caveats.** The window decisions are uncertified CaDiCaL answers, except 6 samples. λ = 21/5
  is the value at the cap, not a limit.

### Files (this section)

| file | contents |
|---|---|
| `counts_sat.py` | full-Q9 counts model: `run` (exact counts), `minsum`, `feasible_sum`, label DFS `dfs`; `report` → `data/counts_report.json`; `concrete` → `data/counts_concrete_*.json` |
| `longwin.py` → `data/longwin_allknown.json` | k-walk counts in G_r = {rc ≤ r}, random G0 window samples (k = 1, 2, 3) decided at radius 4, sample LRAT sizes |
| `ctxcut.py` → `data/ctxcut_allknown_R0.json` | stage 1: 8-direction windows on k6 transitions, lazy loop |
| `ctxcut2.py` → `data/ctxcut2_allknown_R0.json` | stage 2: 9-direction windows on the pair graph (k7 restricted to live k6 states), lazy loop; rounds, 20 removed windows, final cycle |
