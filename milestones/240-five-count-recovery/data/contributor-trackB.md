# Track B: routes to a conditional m <= 220 outside the K7 window-automaton scale-up

Run of 18 November 2026 on one 4-core machine. Solver and Python side only. No certificate was
replayed and no Lean module was built. Track A (`session_01G8dhuETPrC3wjtDMbTB3TW`) scales up the
K7 window automaton plus corner-share route. This track measures the other levers:
(a) new local quantities, (b) better potentials for the quantities the 230 route already uses, and
(c) upper-bound ideas from the literature.

**No bound is claimed.** Every number below is either exact arithmetic or a solver or data
observation, as labelled.

## Summary

| candidate | premise set | best possible bound (evidence) | status for 220 |
|---|---|---|---|
| (b) 230 machinery as is: K7 chain 89/19 + uniform 7-window corner share X | 58,817 windows + 132 share floors | **>= 224 for every X that can be proved**: a real 191-edge snake has a 7-window with corner share 243 (220 needs X >= 345) | **dead** |
| (b) any alpha chain lambda + uniform corner share X | chain + 132 floors | 220 needs 24 lambda + X/7 >~ 156.6, e.g. lambda >= 6.53 at X = 30, lambda >= 5.32 at X = 243 (the real-snake cap) | needs lambda far above the 4.68 frontier (k6 ceiling 9/2) |
| (b) alpha-only chain, cap 8 (`symK 8`) | chain only | real snakes average min(alpha, 8) = 7.357, floor 216 | not excluded in principle; frontier at 4.68 needs 6.68 |
| (a) uniform combined 7-window floor Y on `24 alpha + share12`, **no chain** | 132 shape items | 220 needs Y >= 1133. The real-snake minimum is 1155 (shape `0,1,2,3,4,1,2,0`), and locally valid configurations go lower (see below) | see the sweep section |
| (c) literature (Snevily, Zemor, Solov'eva, Emelyanov-Lukito type) | none | all >= 250 at n = 9 (milestone 22 recomputed them) | dead |

## Exact arithmetic (`trackB/bounds.py`)

The identity is the corner charge `core_charge_sum_le` with M = 12:

    sum_{k=0}^{m} (24 alpha_k + share_k) + 840 (m+1) <= 221136,   alpha_0, alpha_m >= 4.

Each of the three lower bounds below acts on the left side. m is impossible when that bound
exceeds 221136.

- chain `P m <= Q sum_{j=1}^{m-1} alpha_j + C` (K7R34C7W16: 89, 19, 678);
- uniform 7-window share floor X: `sum share >= (m-8) X/7`;
- uniform combined 7-window floor Y: `sum (24 alpha + share) >= (m-8) Y/7` (no chain needed).

Check: 89/19, C = 678 and X = 30 give 230, as in milestone 37.

| target | X needed at 89/19 | Y needed (no chain) |
|---|---|---|
| 229 | 61 | 849 |
| 225 | 184 | 972 |
| 222 | 280 | 1068 |
| 221 | 312 | 1100 |
| 220 | 345 | 1133 |

At 89/19 the chain also gives 230 with X = 60, 228 with X = 100, 227 with X = 150 and 224 with X = 243.

## Real-snake ceilings (`trackB/realstats.py`, `trackB/realshape.py`)

A real snake satisfies every local constraint. So for any window quantity, no floor above the
smallest value seen on a real snake window of that shape can be proved. Data: the 131 bank snakes,
24,890 internal vertices.

- Mean alpha is 8.717 and mean share12 is 99.93.
- Mean min(alpha, c) for c = 6, 7, 8, 9, 10, 12: 5.924, 6.733, 7.357, 7.803, 8.086, 8.422. The
  alpha-only floors are m ~ 224, 219, 216, 214, 212, 211.
- Mean alpha + share/24 is 12.88, a floor of 191: the combined identity is nearly tight on real
  snakes.
- **Minimum 7-window corner share on a real snake: 243.** So the uniform share route cannot pass
  224 at 89/19.
- **Minimum 7-window `24 alpha + share12` on a real snake: 1155**, at shape `0,1,2,3,4,1,2,0`
  (alpha 38, share 243). 220 needs 1133. Of the 132 shapes, 110 occur in the bank; the ten lowest
  real minima are listed in `data/real_shape_min.json`.
- 3-cube census `c(x)` (milestone 22, `sum c <= 64512`): the real mean is 334.4 (20 snakes), the
  minimum 275. 220 would need a mean of 290.6.

## Locally valid configurations below the real snakes (`trackB/cpmin.py`)

`cpmin.py` is a CP-SAT model of exactly the local model of `wincert.Encoding`: radius 4, counts
free, the window selected, degree at most 2, interior degree at least 1, at most 2 ends, no
selected square, no 3-cube 6-cycle, and lazy cuts for cycles inside the ball. It minimises
`sum (wA alpha + share_M)` over the 7 centres. Every reported witness is re-checked as a model of
the `wincert.Encoding` CNF (`sawit.check`, `valid_cnf`).

Shape `0,1,2,3,4,1,2,0` (real minimum 1155):

- **W = 1089 is witnessed**: alpha-sum 36 (counts 5,5,9,4,5,6,2), share 225. The model was found by
  CaDiCaL with lazy cycle cuts on "alpha-sum <= 36 and share <= 235" (`levels.py`, 121-265 s,
  twice). It is cycle-free and a model of the `wincert` CNF (`data/levels.jsonl`). So
  **Y <= 1089 for this shape, and the uniform combined floor gives at best 222.**
- A CP-SAT run reached W = 1083 (alpha 38, share 171). Its selection was not saved and it was not
  re-validated, so it is not used.
- The proved lower bounds are weak: CP-SAT gave lb 702 after 540 s. CaDiCaL at M = 2
  (`combined.py`) proved `W_2 >= 100` and timed out at 140, 150, 170, 175, 195 and 215 within
  280-900 s. The level split proved "alpha-sum <= 44 implies share >= 44" (588 s). Levels 30 and
  40 timed out at 600 s.

**3-cube census mixing does not rescue it.** On the 1089 witness the centres have
`c(x) = 291, 292, 325, 287, 292, 302, 266` (mean 293.6). 220 needs 302.9 per vertex (with the same
(m-8)/(m+1) window accounting), a ratio of 0.969. The corner ratio is 1089/1133 = 0.961. Any
convex combination of the two identities therefore stays below 1 on this window.

## Candidate (a'): a shape-only automaton with per-shape combined floors

This is a new candidate with no counts in the state. States are the 132 canonical
8-direction windows (`shapegraph.py`: 132 shapes, 534 edges, `t = canon(s[1:] + d)`). The step
weight is a per-shape floor `Y(s) <= min W12` over the local models of shape s. A snake's walk then
satisfies `sum_windows Y >= (min cycle mean) * #windows - range`. The premises are just 132 combined
refutations at per-shape levels, with no plain windows at all. The low shape `0,1,2,3,4,1,2,0`
could be avoided if it cannot repeat.

Ceiling test (`ceilloop.py`). U(s) is the smallest validated local W known for shape s: real-snake
windows, then CP-SAT (4 workers, hinted with the best selection, lazy cuts, validated against the
CNF). The loop computes the min cycle mean of U on the shape graph (Lawler/Bellman-Ford) and
improves the witnesses of that cycle's shapes:

- with real-snake minima only (110 shapes): min cycle mean **1382.5** per window, above 1133;
- every CP-SAT improvement so far lands at 1077-1089 per shape (for example `0,1,2,3,1,0,4,3`
  1497 -> 1077 and `0,1,2,3,0,4,3,2` 1497 -> 1085);
- the cycle `01230140, 01230432, 01234210, 01231043, 01203420, 01234120` fell from 1371.5 to
  1232.8 in two improvements (log in `data/ceilloop*.log`).
