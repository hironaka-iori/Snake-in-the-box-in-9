# Ceilings of local window arguments

Checkpoint: 18 October 2026. Status: **computational analysis, not a Lean result.** No bound changes.

## Question

Every upper bound so far is local. It combines the square-incidence identity

`T + 2*s0 = 9214 - 35*v` (snake on `v` vertices; `T` singleton squares, `s0` empty squares)

with lower bounds on `T` derived from windows of consecutive path vertices inside a bounded Hamming ball. This milestone asks how far such arguments can go in principle. The answer comes from configurations that look like a snake in every window but are globally different.

## Real snakes

All 131 bank snakes (`scripts/stats.py`):

- mean internal singleton count `T/v = 8.77`;
- `2*s0/v = 4.22`;
- `(T + 2*s0)/v = 12.99`, the exact value forced by the identity at `v = 192`.

A bound of 196 edges (`v = 197`) needs `(T + 2*s0)/v >= 11.77`. Current Lean bounds use `T/v >= 7/3` and discard `s0`. The conditional automata reach `T/v >= 7/2`.

Charging every empty square to the selected vertices adjacent to it loses nothing on real snakes: every empty square has a selected neighbour (`scripts/s0local.py`). The per-vertex share varies, though: its minimum over internal vertices is 4.0. An empty square touches between 5 and 20 selected vertices.

## An explicit adversary: 224 vertices of 14-cycles

Write `Q9 = Q5 × Q4` and take two vertex-disjoint induced 14-cycles in `Q5` (`scripts/fibre_pair.py`, `data/fibre_pair_q5.json`):

```
A = [0,5,6,7,8,12,14,16,18,19,21,25,27,29]
B = [1,2,3,9,10,13,15,20,22,23,24,26,28,31]
```

Then let `S = { u + 32*y : u ∈ A if popcount(y) is even, u ∈ B if it is odd }`.

Adjacent fibres carry disjoint sets, so `S` induces exactly 16 disjoint 14-cycles. Its properties (`scripts/fibre_build.py`, `data/adversary224.json`):

- `|S| = 224` and every degree is 2;
- `T = 992`, `s0 = 192`, and `T + 2*s0 = 1376 = 9216 - 35*224`;
- singleton counts are 2 (64 vertices), 5 (128) and 7 (32), so the lumped mean is 30/7.

**Window feasibility** (`scripts/win_feas_k.py`). The test uses the radius-r CNF of `milestones/10-window-aggregate/scripts/wincert.py` with exact counts.

| radius | centres | result |
|---|---|---|
| 3 | 2, 3, 4 | all 13 distinct windows SAT (`data/adversary224_radius3.log`) |
| 3 | 5 | refuted by the window with dirs `0,1,2,0,3,2` and counts `(2,5,7,5,2)` (also refuted with lumped counts) |
| 4 | 3, 4 | refuted by the window with dirs `0,1,2,3,4` and counts `(2,5,5,2)` (`data/adversary224_radius4.log`) |

**Consequence for count automata.** Consider an automaton whose states are direction shapes plus singleton counts, with transitions excluded only by refuted radius-3 windows of at most four centres. This is the construction behind the conditional 239. Its periodic walks include those of the 14-cycles of `S`, so its minimum cycle mean is at most 30/7. That caps such a method at about **233 edges** with singleton weights only, and at **223 edges** even if `s0` were counted exactly. The current conditional 239 uses mean 10/3. The levers that remain open are five-centre windows, radius four, and the `s0` term.

**Caveat.** For four-centre windows, the radius-3 ball already contains a whole 14-cycle of `S` (`scripts/ball_cycles.py`). The windows are satisfiable only because the same counts are realized by other local configurations. So the cap applies to arguments that see counts and directions window by window. It does not apply to arguments that keep the joint local configuration.

## A stronger adversary: 208 vertices of 26-cycles

The randomized search `scripts/q6pairs.c` finds two vertex-disjoint induced 26-cycles in `Q6` (`data/fibre_pair_q6.json`). The same fibre rule over `Q9 = Q6 × Q3` (`u + 64*y`) gives `data/adversary208.json`:

- 8 disjoint induced 26-cycles, `|S| = 208`;
- `T = 1328`, `s0 = 304`, and `T + 2*s0 = 1936 = 9216 - 35*208`;
- singleton counts range over 2..10, with lumped mean `69/13 ≈ 5.31`.

| radius | centres | result |
|---|---|---|
| 3 | 2–5 | all distinct windows SAT (`data/adversary208_radius3.log`) |
| 4 | 2–4 | all distinct windows SAT (`data/adversary208_radius4.log`) |

For three-centre windows, no radius-3 ball contains a complete 26-cycle (`data/adversary208_balls.txt`). Every such ball therefore sees only path pieces. No radius-3, three-centre argument of any kind can exclude this configuration locally.

## Floors

All values are in edges and are approximate (`m + 1 ≈ 9214/(35 + μ)`). A real snake is itself a witness: it satisfies every local constraint, so no local argument can prove a smaller weighted mean than real snakes have.

| method family | floor | witness |
|---|---|---|
| any method using only `min(α,6)` (any radius) | ≈ 224 | real bank snakes: lumped mean 5.92 |
| any method using only `α`, without lumping (any radius) | ≈ 209 | real bank snakes: mean 8.77 |
| `α` plus the cheap empty-square charge `2e(x)/21` (radius 3) | ≈ 217.5 | 208-adversary (`scripts/cheap_s0.py`) |
| count/direction automaton, radius 3, ≤4 centres (the conditional 239) | ≈ 233 | 224-adversary |
| count/direction automaton, radius 3 with 5 centres, or radius 4 with ≤4 centres (the conditional 238) | ≈ 227 | 208-adversary |
| the same with `s0` counted exactly | ≈ 207 | 208-adversary |
| any radius-3 three-centre local argument | ≈ 207 | 208-adversary (no complete cycle inside a ball) |

**What this means for the target 196.** Local window arguments cannot get below about 207 unless their radius and state see complete 26-cycles spanning six coordinates. The obstruction comes from fibre unions of long cycles. Fibres over `Q2` would need two disjoint induced cycles in `Q7`, whose total is at most about 96 vertices out of 128 (two 48-coils). That gives at most about 192 vertices, which no longer obstructs 196. So the fibre construction stops mattering only at locality comparable to `Q7`. Below about 207, progress needs either such large localities, with joint configurations and the `s0` term, or a genuinely global argument that uses connectivity: these adversaries have many components, and a snake has one.

## Reproduce

```sh
python scripts/stats.py work/bank9.json
python scripts/fibre_pair.py 5 10 600                 # Q5 pair (CP-SAT)
cc -O2 -o q6pairs scripts/q6pairs.c && ./q6pairs 1 90  # Q6 pair (randomized DFS)
python scripts/fibre_build.py data/fibre_pair_q6.json data/adversary208.json
python scripts/win_feas_k.py data/adversary208.json 3 2 3 4 5
python scripts/ball_cycles.py data/adversary208.json
```

`win_feas_k.py` imports `wincert.py` from `milestones/10-window-aggregate/scripts` and needs `python-sat`.
