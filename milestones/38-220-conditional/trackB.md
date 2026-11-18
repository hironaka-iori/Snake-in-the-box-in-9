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
| (a) uniform combined 7-window floor Y on `24 alpha + share12`, **no chain** | 132 shape items | 220 needs Y >= 1133. A validated local model of shape `0,1,2,3,0,1,4,0` has W = 983, so the route **caps at 225** | **dead** |
| (a') shape-only automaton, 7 centres, per-shape combined floors | 132 items | witnessed min cycle mean 1119.7 < 1133: **caps at 221** | **dead** |
| (a'') shape-only automaton, 9 centres, per-shape combined floors | <= 2,332 items | witnessed min cycle mean 1660.7 after 16 rounds (220 needs 1471); open | ceiling open, **premises out of solver reach** (TIMEOUT at 600-1200 s) |
| (a) 3-cube census mixed with the corner share | + census lemma (not in Lean) | on the W = 1089 witness both identities are below the 220 need (0.969 and 0.961) | no help on the binding windows |
| (b) count-dependent shares in the K7 chain (full LP over the table) | chain + per-(shape, counts) floors | witnesses at alpha ~4.9 with share ~24 per vertex (140 per vertex in total) suggest a cap near 225; the count-consistent test was not conclusive | probably capped at 7 centres |
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
  **Y <= 1089 for this shape**, which alone caps the uniform combined floor at 222. The shape-only
  loop below later found W = 983 on `0,1,2,3,0,1,4,0`, which lowers that cap to 225.
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
  **1119.7 < 1133** in four improvements (`data/ceilloop2.log`). One of them gave shape
  `0,1,2,3,0,1,4,0` a validated local model with **W = 983** (alpha 4,5,4,4,5,5,7, share 167, i.e.
  140 per vertex).

Consequences (all from validated witnesses, so these are ceilings, not estimates):

- **the uniform combined 7-window floor caps at 225** (Y <= 983);
- **the 7-centre shape-only automaton caps at 221** (witnessed min cycle mean 6718/6) and is dead
  for 220. Every further improvement can only lower it.

The logic: U(s) >= the true minimum Y*(s) for every witnessed shape. So the min cycle mean over
witnessed shapes is at least the true min cycle mean over all shapes, which is the most any
per-shape floor can prove.

## Count-dependent shares on 7-centre windows (open)

The remaining 7-centre framework puts per-(shape, lumped counts) share floors inside the K7 chain
(the full LP over the window table). Its ceiling needs a cycle of windows whose **counts agree on
overlaps**. Attempts:

- a coupled CP-SAT over the 6 windows of the cycle above, with one periodic lumped count sequence
  (`jointcycle.py`): after 30 min it still had 87 cuts and a mean of 1818, not informative;
- fixed counts `5,5,5,5,5,5,5` on those windows: one window has a validated model with W = 1069. The
  other plain tests time out at 240 s (CaDiCaL, `fixedsat.py`). These count patterns sit at the
  plain-refutation frontier;
- one global configuration S of Q9 around a fixed induced 32-cycle P (`globalcycle.py`: every window
  along P valid at once, so counts are automatically consistent and P is a cycle of every window
  automaton): CP-SAT reached only 415.7 per vertex in 900 s (all 32 windows validated). This shows
  only that the search is weak.

The per-window witnesses are much denser near the path than any real snake (140 per vertex
against a real minimum of 165). A single structure that is this dense along a whole cycle would be
a union of long paths and cycles of density above 7/16 around P, the plateau of milestone 29.
That is probably impossible, which suggests that **longer windows, not better weights, are the
lever**. A direct check supports this. The 6-cycle of 7-centre shapes above cannot be realised by
10 consecutive directions: every continuation of its direction sequence makes the path non-induced.
So a 9-centre shape automaton removes it on geometry alone, without a solver.

## Candidate (a''): shape-only automaton on 9-centre windows

There are 2,332 canonical 10-direction shapes and 11,437 edges. The threshold for 220 is
Y >= 1471 per 9-centre window (221: 1428, 225: 1262; `bounds.py` with k = 9). The 11-centre version
has 60,577 shapes and needs 1814.

Witnessed ceiling (`ceilk.py 10`, log `data/ceilk10.log`):

- real-snake minima (416 shapes occur): min cycle mean **1942.4**, a 32 % margin over 1471, against
  22 % at 7 centres;
- the CP-SAT improvements are smaller in relative terms. Over 16 rounds the improved shapes
  landed at 1461-1871 (for example 2112 -> 1742, 2112 -> 1676, 1808 -> 1518, 2031 -> 1546), and
  9 of the 16 attempts found nothing below the real value in 150 + 200 s. At 7 centres the shapes
  dropped by about 28 %, to 983-1089;
- after 16 rounds the witnessed min cycle mean is **1660.7**, still above 1471. The loop was still
  descending slowly when it was stopped, so this is not a converged ceiling;
- random 10-direction shapes are far higher (2284, 2408, 2496, 2730, `data/L10_sample_out.jsonl`).
  The low shapes are the compact ones with repeated directions;
- a direct search on the lowest real-occurring shape `0,1,2,3,4,1,2,0,1,3` for a model with
  W <= 1470 (level split, alpha-sum <= 42 and <= 48) found none in 1,200 s each (TIMEOUT). At
  7 centres the same kind of search found its SAT models in 2-4 min.

**Verdict: open at the ceiling level, and the only Track B candidate not yet capped below 220.**
The 1,916 shapes that never occur in a real snake still carry no witness. Since random shapes are
high, they are unlikely to create a lower cycle.

## Truth check and certificate cost (deliverable 2)

The premises of every candidate above are **lower bounds of the form W >= Y** on a window, at
levels of about 1000-1500 M = 12 units. The certificates already produced by the project are of a
different kind: plain exclusions, and share floors of 20-60. Measured costs at the needed levels:

| premise | solver | result |
|---|---|---|
| 7 centres, W_2 >= 140..215 (M = 2, about 840-1290 at M = 12) | CaDiCaL, `combined.py` | 6 TIMEOUT at 280-900 s; only W_2 >= 100 proved (12 s) |
| 7 centres, W12 >= 1100, level alpha-sum <= 44 (share >= 44) | CaDiCaL, `levels.py` | UNSAT, 588 s |
| 7 centres, levels alpha-sum <= 30, <= 40 | CaDiCaL | TIMEOUT at 600 s |
| 7 centres, W12 lower bound by CP-SAT branch and bound | CP-SAT, 4 workers | lb 702 after 540 s (1100 needed) |
| 9 centres, W12 >= 1471, level alpha-sum <= 60 (share >= 31) | CaDiCaL | UNSAT, 0.5 s |
| 9 centres, levels <= 55, <= 50 | CaDiCaL | TIMEOUT at 600 s |
| 9 centres, levels <= 48, <= 42 | CaDiCaL | TIMEOUT at 1,200 s |

No sampled premise came out SAT at a level a live candidate needs. On the SAT side, the 7-centre
uniform and shape-only candidates were killed by validated witnesses (above). On the UNSAT side,
almost every premise beyond the top alpha level times out at 10-20 min. Estimate for the 9-centre
candidate: 2,332 shapes times about 25 alpha levels is about 58,000 items. Most are above the
20-minute mark and of unknown size, so **the certificate cost cannot be bounded today**. It is at
least 10^7 CPU-seconds even if every item finished at the measured timeout, and the real risk is
items that never finish. That is not competitive with Track A's route, where every premise is
either already a DRUP-verified plain window or a share floor of a few dozen.

## Lean (deliverable 3): not attempted

No Track B candidate is live for 220 with a feasible premise set:

- the 7-centre candidates (uniform share, uniform combined, shape-only) are capped at 224, 225 and
  221 by witnesses;
- the 9-centre shape-only candidate is open at the ceiling level, but its premises are out of
  solver reach.

So no `Snake9.upper_2XX_of_...` theorem was written. Writing one would mean stating a conditional
theorem on premises that cannot currently be certified, and the arithmetic wrapper alone (a new
combined-weight bridge plus `core_charge_sum_le`) is not the bottleneck.

## Conclusions for the 220 programme

1. **The 230 machinery itself stops at 224** (89/19 + uniform corner share), on real-snake data
   alone. No LP re-weighting of a uniform share floor changes that: 220 needs
   24 lambda + X/7 >~ 156.6 and X <= 243.
2. **Every count-free 7-centre use of the corner identity is capped at 221-225** by validated local
   models (W = 983 and a witnessed cycle mean of 1119.7). Those models have alpha mean ~4.9, above
   the K7 chain's 4.68, and only ~24 share per vertex. So count-dependent share floors on 7-centre
   windows very probably hit the same wall, unless such windows cannot chain with consistent
   counts. The exact test (`jointcycle.py`, `globalcycle.py`) is built, but its CP-SAT runs were too
   weak to conclude.
3. **The lever is window length.** The worst 7-centre witness cycle cannot be extended to 10
   directions at all, and 9-centre per-vertex minima found so far are 162-208 (1461-1871 per
   window), against 140-160 at 7 centres and the 163.4 that 220 needs at 9 centres.
4. **The blocker is proof cost, not soundness.** Lower bounds at combined levels of about 1100-1500
   are out of reach for CaDiCaL and CP-SAT at 10-20 minutes per item. A route to 220 through window
   floors needs either a far cheaper encoding of the combined weight (for example a per-centre
   decomposition that reuses plain exclusions for the low-alpha part), or windows long enough
   that plain exclusions alone drive alpha (cap 8) to about 6.7, which real snakes allow (7.357).
5. (c) The literature bounds are all >= 250 at n = 9 (milestone 22) and add nothing.

## Files (`trackB/`)

| file | content |
|---|---|
| `bounds.py` | exact arithmetic of the chain, uniform share and uniform combined floors (any k) |
| `realstats.py`, `realshape.py` | real-snake per-vertex statistics and per-shape window minima |
| `combined.py` | CNF of the combined weight (wincert + share clauses + weighted alpha literals in one totalizer) |
| `levels.py` | split of W >= Y by alpha-sum levels (ShareEncoding + at-most-a), with witnesses |
| `cpmin.py`, `cpbatch.py` | CP-SAT minimiser of the combined weight in the wincert local model, lazy cuts, CNF validation |
| `sa.c`, `sawit.py`, `seeds.py`, `ceil7.py` | annealing witnesses seeded from real snakes (weaker than CP-SAT) |
| `shapegraph.py` | canonical shape graphs (132 shapes / 534 edges at 7 centres, 2,332 / 11,437 at 9) |
| `ceilloop.py`, `ceilk.py` | witnessed-ceiling loops of the shape-only automata |
| `jointcycle.py`, `fixedcounts.py`, `fixedsat.py`, `globalcycle.py` | count-consistent ceiling tests (inconclusive) |
| `w3.py` | 3-cube census weight c(x) |
| `data/witness_W24.jsonl`, `data/witness_L10.jsonl` | every validated witness (selection included) |
| `data/levels.jsonl`, `data/lv10_*.out` | level-split SAT/UNSAT records |
