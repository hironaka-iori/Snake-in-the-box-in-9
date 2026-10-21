# The empty-square term s0 as a route towards 196: what local arguments can and cannot do

Notes of 19 October 2026 (static analysis; small Python runs, each under 2 minutes of CPU; nothing here is a Lean theorem). The scripts are in `milestones/11-local-ceiling/scripts/s0lever/`:
- `charges.py`, `stats_all.py` and `summary.py` compute the charges and their statistics.
- `pump.py` computes caps from repeated states in real snakes.
- `caps.py`, `thresholds.py` and `symcaps.py` compute symbol caps and window lengths.
- `misc.py` checks the identities and ball sizes.
- `forced_s0.py` is a small SAT probe. It uses Glucose4, not CaDiCaL.

## 0. The definitions match Lean, and the identity holds

- Lean's `singleton` (`work/spectral/SquareIncidence.lean:68-70`) is the same as `alpha(x)`: the number of pairs {a,b} for which x is selected and x^a, x^b and x^ab are all unselected.
- Lean's `empty` (`:75-77`) is anchored at every corner. So `totalEmptyAnchored` (`:108`) equals 4·s0, and it also equals Σ_q e0(q), where e0(q) is the number of empty squares containing q.
- `global_identity` (`:110-112`) states 2E + 4T + 144v = 36864 + 4W. Together with `wedge_total_upper` (`:231`), this gives T + 2·s0 ≤ 9214 − 35v. For a snake it is an equality, because W = v − 2.
- **Checked numerically:**
  - Bank snake 0 has v = 192, T = 1682, s0 = 406, and T + 2s0 = 2494 = 9214 − 35·192.
  - All 131 bank snakes satisfy the identity (assert in `charges.py`).
  - adv208 and adv224 satisfy 9216 − 35v, because W = v for a union of cycles.
- **Two further identities**, checked on bank snake 0:
  - alpha(x) = 23 − d2(x) at path indices 2..v−3, where d2(x) is the number of selected vertices at distance 2 from x.
  - s0 = 4602 − 29v + D2 and T = 10 + 23v − 2·D2, where D2 is the number of selected pairs at distance 2.
  - So T + 2s0 does not depend on D2. **An exact local charge carries no information beyond v.** A local proof of Σγ ≥ μv is a proof that snakes cannot be packed densely. Its floor is the vertex count of the densest configuration that the method cannot tell apart from a snake.

## 1. Per-vertex charges γ = α + (share of the empty squares)

Every rule below is a valid lower bound: Σ_x γ(x) ≤ T + 2s0.

| rule | support | definition | exact when |
|---|---|---|---|
| **ex** | radius 4 | each empty square Q gives 2/\|N(Q)∩S\| to every selected vertex next to Q | no empty square is without a selected neighbour (true on all 133 configurations) |
| **dom (corner rule, proposed)** | **radius 3** | each unselected q gives e0(q)/(2·d(q)) to each of its d(q) selected neighbours | every corner of an empty square has a selected neighbour |
| c3 | radius 3 | Q empty and x in the parallel square Q^k with t selected vertices: 2/(7t) | never |
| cheap | radius 3 | 2e(x)/21 (`milestones/11-local-ceiling/scripts/cheap_s0.py:13`) | never |

Why the **dom** rule is the one to use:
- It sums to Σ_{q dominated} e0(q)/2 ≤ `totalEmptyAnchored`/2. That is a single double-counting lemma on top of `SquareIncidence.lean`.
- An integer version avoids fractions in Lean. Give each neighbour shareN(x) = Σ_q ⌊M·e0(q)/d(q)⌋. Then Σ_x (4M·α(x) + 2·shareN(x)) ≤ M(36856 − 140v), from `:110-112` and `:231`.
- It is exact on both adversaries.
- On the bank it loses 98.5 units in total over 131 snakes, about 0.75 per snake out of 2494.
- d(q) reaches 7 on real snakes and on adv208, so dividing by d(q) is needed. A fixed linear weight would throw away most of the share.

Means over all vertices, minima over internal vertices, and the floor 9214/(35+μ) − 1 in edges:

| | bank (v=192, 131 snakes) | adv208 | adv224 |
|---|---|---|---|
| α: mean / min | 8.77 / 3.00 (floor 209.5) | 6.38 / 2 (221.6) | 4.43 / 2 (232.7) |
| ex: mean / min | 12.99 / 3.45 (191.0) | 9.31 / 2.71 (**207.0**) | 6.14 / 2.81 (**223.0**) |
| **dom: mean / min** | **12.986 / 3.33** (191.0) | **9.31 / 2.54** (207.0) | **6.14 / 2.61** (223.0) |
| c3: mean / min | 12.82 / 3.38 (191.7) | 8.91 / 2.76 (208.8) | 5.90 / 2.86 (224.3) |
| cheap: mean / min | 11.33 / 3.38 (197.9) | 8.25 / 2.67 (212.0) | 5.64 / 2.76 (225.7) |
| minimum mean of dom over k consecutive vertices, k = 2/4/6/10/20/40 | 4.91 / 5.99 / 6.55 / 8.52 / 10.06 / 10.95 | 4.94 / 5.12 / 6.41 / 7.70 / 8.60 / – | 4.42 / 4.42 / 5.17 / 5.81 / – |

**The s0 share sits mostly at vertices that already have high α.** For dom − α on bank internal vertices:

| α | min share | mean share |
|---|---|---|
| 3 | 0.33 | 0.74 |
| 4 | 0.65 | 0.87 |
| 6 | 1.02 | 1.70 |
| 8 | 1.50 | 3.00 |

On the adversaries, vertices with α = 2 get 0.54–0.61. So s0 lifts the low-α cycles that currently bind the automaton by only about 0.3–0.9 per vertex.

**Minor correction to milestone 11.** The milestone 11 README says the minimum per-vertex value of α + share over internal vertices is 4.0 (`milestones/11-local-ceiling/README.md:23`). That figure comes from `bank[:40]` (`s0local.py:6`). Over all 131 snakes the minimum is 3.45, at bank snake 45, index 179, where α = 3.

**Real snakes do not cap the automaton.** Take an automaton whose states are the last L direction shapes plus the last K symbols. A segment of a bank snake that returns to the same state would form a cycle in that automaton (`pump.py`). For exact or half-integer dom symbols, every such cycle has mean at least 12.4, from L6K3 up to L20K18. So **the binding obstructions are only non-snake configurations that look locally like snakes** (the adversaries). For lumped α the same test gives 5.20 at L6K3, consistent with the proved 10/3.

**s0 needs radius 4.** I built the existing `wincert` CNF (`milestones/10-window-aggregate/scripts/wincert.py:60-123`) and added an indicator for each empty square at the centre's 7 unselected neighbours.
- One centre at radius 3 with α ≤ 3 is forced **0** empty-square incidences, even with α unconstrained.
- The middle centre of a 3-centre window with dirs 0120 and α ≤ 3 is forced only 2.
- This matches `milestones/10-window-aggregate/README.md:124`: at radius 3 nothing is forced, while at radius 4 a vertex of count one forces at least 4 empty squares.
- The reason: the dom support reaches distance 3 from the centre. In the radius-3 model those vertices are on the boundary and largely free, so the solver can fill every empty square.
- A radius-4 single-centre minimisation did not finish within my 100 s limit on this loaded machine.

## 2. What each target needs, and whether the adversaries already rule it out

μ is the mean needed to exclude v = X + 2. The cap G is the smallest value such that the mean of min(dom, G) exceeds μ. "k-window" is the shortest window whose minimum mean on bank snakes exceeds μ, which a plain sliding-window proof would need.

| bound | μ needed | cap G: bank / adv208 | k-window on bank | blocked by | locality needed |
|---|---|---|---|---|---|
| 230 | 4.716 | 4.75 / 5.25 | 2 | nothing known (adv224 at 6.14, adv208 at 9.31) | radius 4, so that s0 is forced at all |
| 220 | 6.505 | 6.75 / 7.5 | 6 | **adv224 (6.14)** | refute adv224: radius 3 with 5 centres, or radius 4 with 3–4 centres (`11-local-ceiling/README.md:46-48`). Lumped α ≤ 6 alone cannot reach it, since bank gives 5.98 |
| 210 | 8.462 | 9 / 11.5 | 10 | adv224; adv208 only if symbols are coarse | as for 220. Integer symbols: ⌊min(dom,12)⌋ gives 8.31 on adv208 and fails; ⌊min(dom,16)⌋ gives 8.77 and works |
| 207 | 9.086 | – | – | **adv208 (9.31): a hard floor** | any method that cannot refute adv208: radius 3 with ≤5 centres, or radius 4 with ≤4 centres (`:62-65`) |
| 200 | 10.614 | 12.75 / never | 33 | adv208 (and adv224) | windows that contain whole 26-cycles: radius 3 with 6 centres, radius 4 with 4, or radius 5 with 3 (`data/adversary208_balls.txt:4,6,9`). Their balls cover 312, 396 and 459 of the 512 vertices |
| 196 | 11.535 | 16.25 / never | **88** | adv208, plus any configuration that looks locally like a snake and has v ≥ 198 | the same near-global windows. Integer symbols with cap 20 give 196.6 on the real snakes themselves |

**What cannot work, stated plainly:**
- Window arguments that cannot exclude adv208 stop at 207 edges, whatever the s0 charge is.
- Seeing a whole 26-cycle is necessary but not sufficient: the radius-4 count windows with ≤4 centres are all SAT (`adversary208_radius4.log`).
- For 196, every configuration of v ≥ 198 vertices that looks locally like a snake must be excluded. Let M(g) be the largest union of induced cycles in Q9 whose cycles all have length at least g. Then M(14) ≥ 224 and M(26) ≥ 208. Fibre constructions over Q7 stop at 192 (`11-local-ceiling/README.md:83`), but M(g) for 30 ≤ g ≤ 50 is unknown.
- If M(g) ≥ 198 for large g, then 196 needs a global argument using connectivity, not windows.
- **Realistic gain from s0:** take the radius-4 automaton at 42/11, which gives 236 (`10-window-aggregate/README.md:114`), and add roughly +0.3 to +0.9 for the forced share. That gives about 231–234 edges. 230 is borderline.

## 3. Proposed next experiment (a few CPU-hours, under 2 GB, single-threaded at nice 19)

**E1: does s0 pay off at radius 4? (about 2–3 CPU-hours)**
1. Add to a scratch copy of `wincert.Encoding` an indicator E_{q,ab} for each empty square at the centre's unselected neighbours. Also add a one-hot encoding of d(q), and a totalizer bound on shareN = Σ_q ⌊2·e0(q)/d(q)⌋. That is M = 2, a resolution of 1/4 in share.
2. At radius 4, find the minimum shareN for a single centre with α = 1..6. Then do the same for 2- and 3-centre windows, using the shapes and counts on the minimum cycles in `data/refine_L7_k5_K5_r4.json`. Use binary search with an incremental solver.
3. Add these minima to the worst cycles of that automaton. If the predicted mean reaches about 4.72, the 230 route is worth building in Lean: an Axioms share field, its bridge, the clause kinds in `gen_lean_sat.py`, and the double-counting lemma. If the predicted mean stays near 4.2, stop.

**E2: lower bounds on M(g) (about 1–2 CPU-hours, no SAT)**
- Run a randomized search for disjoint induced 2-regular subgraphs A and B of Q7 with all cycles of length at least g and |A| + |B| ≥ 99. Through the fibre rule over Q7×Q2, this gives a union of cycles in Q9 with v ≥ 198. Extend `q6pairs.c` for this.
- Also run a direct annealing search in Q9 for g ∈ {28, 32, 40, 48}.
- A hit settles that local windows cannot reach 196 below that girth.