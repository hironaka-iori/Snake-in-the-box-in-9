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
