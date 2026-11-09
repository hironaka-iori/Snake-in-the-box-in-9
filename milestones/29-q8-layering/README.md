# Layering through induced linear forests in Q8

Run of 9 November 2026. One core at nice 15, about 5 hours.

**Status:** exact small tables, construction data, a few SAT-proved upper bounds (g7(c) ≤ 57 for c ≤ 8, g8(c) ≤ 121 for c ≤ 14), and an assessment. Nothing here is a Lean theorem, and no bound on a(9) changes.

## Question

Cut Q9 along a coordinate. Each half of a snake is then an induced linear forest in Q8. Milestone 22 reduced the layer argument to the numbers `g8(c)`, the largest induced linear forest of Q8 with at most c paths, and found that 236 needs `g8(13) + g8(14) ≤ 237`. This milestone asks three things:

- How tight is layering?
- What can be proved about `g8`?
- Is layering a route below 234, or below the local ceiling of about 227?

## The inequality

The full derivation is in [derivation.md](derivation.md). A snake with m edges that uses direction i exactly k times splits into k + 1 pieces. The pieces alternate between the halves: `floor(k/2)+1` lie in the half holding the first piece and `ceil(k/2)` in the other.

- Every internal piece has at least 3 vertices. A 1-vertex internal piece would need two equal path neighbours. A 2-vertex internal piece gives a chord.
- So for k even, the second half has no short piece. For k odd, each half has at most one.
- The least-used direction has `k ≤ floor(m/9)`. Hence

```
m + 1 ≤ max_{k ≤ floor(m/9)}  g3_8(floor(k/2)+1, t_a) + g3_8(ceil(k/2), t_b)
```

Here `g3(p, t)` allows exactly p paths, at most t of them with fewer than 3 vertices, with `(t_a, t_b) = (2, 0)` for k even and `(1, 1)` for k odd. Any upper bound for `g(p)` may be used in place of `g3`.

Parity facts (`k_i ≡ u_i + w_i` for the end vertices; the number of odd `k_i` is `d(u, w) ≡ m`) only choose between the two `(t_a, t_b)` cases. The edge-count variant is equivalent with exact piece counts and weaker with "at most".

What the inequality demands at n = 9, given the Lean bound a(9) ≤ 235 (G is monotone, so only k = 24, 25, 26 matter; see the ladder in §4):

| target | conditions |
|---|---|
| a(9) ≤ 234 | g8(13) + g8(14) ≤ 235 |
| a(9) ≤ 233 | g8(14) ≤ 117 |
| a(9) ≤ 227 | g8(13) ≤ 114 and g8(14) ≤ 117 |
| a(9) ≤ 223 | g8(13) ≤ 112 and g8(14) ≤ 122 |

## 1. Exact values for n = 4, 5, 6 (`gforest.py`, `gtable.py`; data in `data/g{4,5,6}.jsonl`)

The values come from SAT with CaDiCaL 1.9.5 through python-sat. The encoding has these parts:

- degree at most 2;
- exact endpoint indicators, where an isolated vertex counts twice;
- all 4-cycles and the induced 6-cycles of 3-subcubes forbidden;
- longer cycles excluded either lazily or by a level encoding (`--levels`): every internal vertex has a selected neighbour of smaller level;
- symmetry breaking: a longest path starts 0, e0, e0+e1, e0+e1+e2, and its fifth vertex is e1+e2 or e0+e1+e2+e3.

| c | g4 | g5 | g6 | g6, exactly c paths, ≤ 0 short |
|---|---|---|---|---|
| 1 | 8 | 14 | 27 | 27 |
| 2 | 8 | 14 | 28 | 28 |
| 3 | 8 | 15 | 28 | 28 |
| 4 | 8 | 16 | 28 | 28 |
| 5 | 8 | | 29 | 28 |
| 6 | 8 | | 30 | 28 |
| 7 | 8 | | 31 | 29 |
| 8 | 8 | | 32 | 32 |

For n ≥ 5, Huang's theorem caps everything at `2^(n-1)`. Every Q6 query takes under 1 s.

Cross-checks:
- Lazy cuts and the level encoding agree.
- Weaker symmetry levels agree. Translation plus the first edge alone takes 8–43 s per query; without symmetry breaking a single Q6 query takes more than 1500 s.
- The exactly-c and short-piece variants (`g_eq`, `g3_short*` in the data) change nothing in the calibrations.

## 2. Calibration: how tight layering is (`layer.py`)

| N | layering bound, edges | truth a(N) | over by |
|---|---|---|---|
| 5 | 15 (exact g4) | 13 | 15 % |
| 6 | 28 (exact g5) | 26 | 8 % |
| 7 | 56 (exact g6) | 50 | 12 % |
| 8 | 111 if g7 equals its lower bounds below; **113 proved** (§4) | 98 | 13 % (proved: 15 %) |
| 9 | **223** if g8 equals its lower bounds below | 191–235 | — |

Two cuts (quarters, Q_{N-2}) are useless: 31 at N = 6 and 63 at N = 7, both Huang. At N = 9 it gives 246 even with g7 equal to its lower bounds, because `g7(13) ≥ 61`.

## 3. Lower bounds and the plateau (`forest_sa.c`, data in `data/sa_lower.jsonl`)

Simulated annealing reproduces every exact Q6 value and g7(1) = 51, and it finds 98 for g8(1), one below the true 99. The witnesses are re-checked by `check_forest`.

- g7 ≥ 51, 52, 53, 56, 56, 56, 56, 56, 57, 58, 59, 60, 61, 62, 63, 64 for c = 1..16.
- g8 ≥ 99, 99, 99, 104, 104, 106, 106, and 112 for every c from 8 to 16, then 96 + c for c from 16 to 32. The 96 + c comes from deleting isolated vertices of the c = 32 witness, which is 16 copies of P7 plus 16 isolated vertices.

The data show a clear pattern, a **plateau at 7·2^(n-4)**:

| n | plateau value | plateau range of c | witness structure |
|---|---|---|---|
| 5 | 14 | c = 1–2 | |
| 6 | 28 | c = 2–4 | four P7 |
| 7 | 56 | c = 4–8 (lower bounds) | four P14 or eight P7 |
| 8 | 112 | c = 8–16 (lower bounds) | eight P14 or sixteen P7 |

Above the plateau, each extra path adds exactly one isolated vertex up to `2^(n-1)`, so `g_n(c) = 3·2^(n-3) + c` there. This holds exactly for n = 5 and 6.

In Q8, annealing runs of 4·10^8 steps found nothing above 112 for any c in 8–20, and neither did a 15-minute SAT search for 113 vertices with 17 paths. But for c = 17–20 the construction above gives 113–116, so these searches are blind at exactly this level. **The evidence for the plateau in Q8 is therefore the pattern, not the searches:**
- exact in Q5 and Q6;
- in Q7, lower bounds of 56 throughout c = 4–8, against the proved upper bound 57;
- the matching 7·2^(n-4) constructions.

**Conjecture P:** g8(c) = 112 for 8 ≤ c ≤ 16. If it holds, layering gives **a(9) ≤ 223 edges**. That is below the local-window ceiling of 222–227 and far below 234. It only needs `g8(13) ≤ 112`, because `g8(14) ≤ 121` is proved below.

## 4. What is actually provable about g8

- **Huang:** g8(c) ≤ 128 for every c. This is tight at c = 32.
- **Recursive layering** (`recursion.py`, `data/recursion.json`):
  - From the exact g6 table it gives g7(c) ≤ 57, 58, …, 63 for c = 1..7, and 64 from c = 8 on.
  - From those values it gives g8(c) ≤ 128 for every c.
  - The least-used direction of a forest with c paths and f vertices still produces c + (f − c)/8 pieces. So even exact g7 values give only g8(13) ≤ 2·g7(13), and g7(13) ≥ 61.
  - Cutting a forest does not preserve "few paths". The loss that the snake inequality suffers once compounds at every level.
- **Spectral and counting:** the Huang interlacing argument does not see the number of paths, because every forest has λ1 < 2 < √8. The higher-moment identities reproduce the square census (milestone 22). Subcube-local versions average out: `e(F ∩ Q6) ≤ 24` whenever a Q6 holds at least 4 pieces, which gives e(F) ≤ 128 at best.
- **Direct SAT** (level encoding, symmetry breaking; `data/q7_runs.txt`, `data/q8_runs.txt`):

| query (≤ c paths, ≥ L vertices) | result | time |
|---|---|---|
| Q7, c = 8, L = 60 / 59 / 58 | UNSAT | 39 s / 226 s / 1606 s |
| Q7, c = 8, L = 57 (the plateau value + 1) | unknown | > 2400 s (lazy cuts, levels, and levels + implied Q6 tables all fail) |
| Q8, c = 14, L = 127 / 126 / 125 / 124 | UNSAT | 53 s / 76 s / 136 s / 501 s |
| Q8, c = 14, L = 123 | UNSAT | 1517 s |
| Q8, c = 14, L = 122 | UNSAT | 3327 s |
| Q8, c = 14, L = 121 | unknown | > 6000 s (run lost at a container restart) |

  **Proved here:** g7(c) ≤ 57 for c ≤ 8, against the lower bound 56, and g8(c) ≤ g8(14) ≤ 121 for c ≤ 14, against the lower bound 112.

  Neither the implied subcube tables nor sorting the free coordinates by edge count helped: 72 s against 39 s, and 236 s against 226 s.

**Implied bounds.**

- *N = 8 (calibration).* With g7(c) ≤ 57 for c ≤ 8, layering **proves a(8) ≤ 113** (truth 98). Only c ≤ 8 is needed, since floor(127/8) = 15 gives at most 8 pieces per half. The input is one SAT run (1606 s) that the same LRAT pipeline could certify; no LRAT was produced here.
- *N = 9.* With what is proved (g8(c) ≤ 121 for c ≤ 14, and Huang's 128 beyond), layering gives **a(9) ≤ 241**. That is far weaker than the Lean bound of 235.

Ladder of what would follow from proved values (`layer.py`, `ladder()`, using a(9) ≤ 235):

| proved g8(c) for c ≤ 13 | proved g8(14) | a(9) ≤ |
|---|---|---|
| 117 | 118 | 234 |
| 117 | 117 | 233 |
| 116 | 117 | 231 |
| 115 | 117 | 229 |
| 114 | 117 | 227 |
| 113 | 117 | 225 |
| 113 | 121 (proved) | 234 |
| 112 | 121 (proved) | **223** |

Since g8(14) ≤ 121 is now proved, **a(9) ≤ 223 follows from the single statement g8(13) ≤ 112** (together with the Lean bound 235). That statement is the Q8 case of the plateau. Without it, the cheapest improvement is g8(14) ≤ 117, which gives 233.

## 5. Assessment

- **Layering is potentially strong, not weak.**
  - Milestone 22 put the exact-data value somewhere in 224–255.
  - The exact Q6 table and the plateau seen in Q7 and Q8 put it at **about 223** if Conjecture P holds.
  - The calibration is 8–15 % above the truth at N = 5–8.
  - The gain comes from the plateau, a global effect: few paths cost 2^(n-4) vertices against Huang. Windows cannot see it. So layering is the one known route below the 222–227 local ceiling, as the question anticipated.
- **The bottleneck is purely computational.**
  - Every useful step needs an exhaustive statement about Q8 forests with 13–14 paths.
  - The first step that improves on 235 is g8(14) ≤ 117 (giving 233). That is 4 vertices below what is proved today (121), and 5 above the conjecture.
  - On one core, the run times for L = 127, 126, …, 122 are 53, 76, 136, 501, 1517 and 3327 s, so each further vertex costs a factor of 2–4. In Q7 the factor rose to 6–7 within 2–3 vertices of the optimum. A rough extrapolation for L = 118, that is g8(14) ≤ 117, is 10^5–10^6 core-seconds: core-days to core-weeks. **That is a realistic target** for a long single run or a modest parallel cube-and-conquer, and it would give a(9) ≤ 233.
  - The tight value g8(13) ≤ 112, which is what 223 needs, looks harder than the Q7 plateau g7(8) ≤ 56, which this encoding cannot settle in 40 min.
  - The two-cut variant needs only Q7, but it is dead: g7(13) ≥ 61, so 4·61 > 236.
- **What a rigorous version needs:**
  1. A scalable Q8 search. Candidates:
     - cube-and-conquer, for example on the restriction to a Q6 or Q7 subcube, using the exact smaller tables as pruning constraints;
     - better acyclicity encodings;
     - full orbit-based symmetry breaking (the group has order 2^8·8!; only the path prefix is fixed now).
  2. Settle the Q7 plateau g7(8) = 56 first, as a stepping stone and to test Conjecture P.
  3. Certification as in the existing chain. The decision problem is a single CNF: base encoding plus level encoding, or base plus cycle cuts (each cut checkably spans a cycle of Q_n). CaDiCaL emits LRAT, which the Lean kernel checks, as for the window certificates.
     - Lean lemmas needed: (i) the halves of a snake are induced linear forests with floor(k/2)+1 and ceil(k/2) pieces, internal pieces with at least 3 vertices; (ii) the level encoding is sound (a cycle has a minimum level); (iii) the symmetry normalisation; (iv) the arithmetic of the ladder.
     - Demonstration: the Q6 instances g6(4) ≤ 28 and g6(1) ≤ 27, written as single CNFs (levels, about 11k variables and 25k clauses), give LRAT proofs of 3.4–3.7 MB in under 1 s with the toolchain CaDiCaL (`--lrat`, checked online by its LRAT checker).
     - At a similar proof rate, the 500–1500 s Q8 runs would give proofs of several GB, so the LRAT for the hard Q8 instances would be very large. Reasonable as a stored artifact only if the instance solves in core-days rather than core-years.

## Files

- `derivation.md`: the inequality with endpoints, short pieces, parity, two cuts and the forest recursion.
- `scripts/gforest.py`: SAT encoder and solver. It supports lazy cycle cuts or levels, the exact and short variants, symmetry breaking, and implied subcube tables.
- `scripts/gtable.py`: exact tables. `scripts/show.py` prints them.
- `scripts/layer.py`: the one-cut and two-cut calculators, the calibrations, and the bounds from lower-bound tables.
- `scripts/recursion.py`: recursive upper bounds for g7 and g8.
- `scripts/forest_sa.c`: simulated annealing, used for lower bounds only (`gcc -O2 -o forest_sa forest_sa.c -lm`).
- `scripts/run_query.py`: one level-encoded SAT query (Q7/Q8 runs).
- `data/g4.jsonl`, `data/g5.jsonl`, `data/g6.jsonl`: exact tables, with witnesses and solver logs.
- `data/sa_lower.jsonl`: lower-bound witnesses for Q7 and Q8.
- `data/recursion.json`, `data/q7_runs.txt`, `data/q8_runs.txt`: recursion output and the Q7 and Q8 SAT runs.
