# Layering through induced linear forests in Q8

Run of 9 November 2026. One core at nice 15, about 4 hours.

**Status:** exact small tables, construction data, and an assessment. Nothing here is a Lean theorem, and no bound changes.

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

What the inequality demands at n = 9, given the Lean bound a(9) ≤ 235:

| target | conditions |
|---|---|
| a(9) ≤ 234 | g8(13) + g8(14) ≤ 235 |
| a(9) ≤ 230 | g8(13) ≤ 115 and g8(13) + g8(14) ≤ 234 |
| a(9) ≤ 226 | g8(13) ≤ 113 and g8(13) + g8(14) ≤ 234 |
| a(9) ≤ 223 | g8(12), g8(13) ≤ 112 and g8(13) + g8(14) ≤ 234 |

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
| 8 | 111 if g7 equals its lower bounds below | 98 | 13 % |
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

In Q8, annealing runs of 4·10^8 steps, and a 15-minute SAT search for 113 vertices with 17 paths, found nothing above 112 for any c in 8–20.

**Conjecture P:** g8(c) = 112 for 8 ≤ c ≤ 16. If it holds, layering gives **a(9) ≤ 223 edges**. That is below the local-window ceiling of 222–227 and far below 234. It only needs `g8(13) ≤ 112`, with `g8(14) ≤ 122`.

## 4. What is actually provable about g8

- **Huang:** g8(c) ≤ 128 for every c. This is tight at c = 32.
- **Recursive layering** (`recursion.py`, `data/recursion.json`):
  - From the exact g6 table it gives g7(c) ≤ 57, 58, …, 63 for c = 1..7, and 64 from c = 8 on.
  - From those values it gives g8(c) ≤ 128 for every c.
  - The cut in the least-used direction produces about c + (f − c)/8 pieces, so even exact g7 values would give g8(13) ≤ 2·g7(13) ≥ 122.
  - Cutting a forest does not preserve "few paths". This is the same loss that makes the snake inequality lossy, but it compounds.
- **Spectral and counting:** the Huang interlacing argument does not see the number of paths, because every forest has λ1 < 2 < √8. The higher-moment identities reproduce the square census (milestone 22 §0–3). The subcube-local version, `e(F ∩ Q6) ≤ 24` when a Q6 holds at least 4 pieces, averages to e(F) ≤ 128.
- **Direct SAT:**
  - The Q6 plateau claims (g6(4) ≤ 28 and so on) take under 1 s with symmetry breaking.
  - The Q7 analogue g7(8) ≤ 56 (no forest with 57 vertices and at most 8 paths) is **unresolved** after 40 min with lazy cuts and after 40 min with levels, and also with the implied constraints `|F ∩ Q6| ≤ g6(#pieces)` on all 14 halves. See `data/q7_runs.txt`.
  - Q8 at 113–118 vertices with 13–14 paths is far beyond that.

**With what can be proved today, layering gives a(9) ≤ 255.** The values g8(1) = 99 (from a(8) = 98, a literature result not checked in Lean) and Huang's 128 are all there is. That is far weaker than the Lean bound of 235.

## 5. Assessment

- **Layering is potentially strong, not weak.**
  - Milestone 22 put the exact-data value somewhere in 224–255.
  - The new data, the exact Q6 table and the plateau seen in Q7 and Q8, put it at **about 223** if Conjecture P holds.
  - The calibration is 8–15 % above the truth at N = 5–8.
  - The bound comes from the plateau, which is a global feature: few paths cost 2^(n-4) vertices against Huang. Local windows cannot see it.
- **The bottleneck is purely computational,** and it is severe.
  - Proving any useful bound needs `g8(13) + g8(14) ≤ 235` (for 234), down to `g8(13) ≤ 112` (for 223). These are exhaustive statements about Q8 with 13–14 paths.
  - Our pipeline gains a factor of more than 1000 from Q6 to Q7 and still fails on Q7. A naive Q8 instance is out of reach, and so is a(8) = 98-scale effort.
  - The two-cut variant needs only Q7, but it is dead: g7(13) ≥ 61 gives 4·61 > 236.
- **What a rigorous version would need:**
  1. A Q8 search that scales. Candidates:
     - cube-and-conquer over the restriction to one Q7 half, using the exact Q7 tables as pruning constraints;
     - a symmetry-reduced orbit enumeration of the 13–14 pieces' endpoint sets;
     - stronger implied constraints, such as Q6- and Q7-subcube tables and the Huang 2^(k-1) caps.
  2. Proving the Q7 plateau first (g7(c) ≤ 56 for 4 ≤ c ≤ 8) as the test case.
  3. Certification as in the existing chain. Each leaf is a CNF: the base encoding, plus cycle cuts (a cut is valid if its vertex set spans a cycle of Q_n, which is decidable), or the level encoding, whose soundness is a short lemma about minima. CaDiCaL then gives LRAT, which the Lean kernel checks. The lemma that "the halves are induced linear forests with that many pieces, internal pieces of at least 3 vertices" is elementary.
  4. A cheaper intermediate: `g8(13) ≤ 117` and `g8(14) ≤ 118` already give a(9) ≤ 234. They have 5–6 vertices of slack over the conjecture, but slack did not make the Q7 analogue easy either (`data/q7_runs.txt`).

## Files

- `derivation.md`: the inequality with endpoints, short pieces, parity, two cuts and the forest recursion.
- `scripts/gforest.py`: SAT encoder and solver. It supports lazy cycle cuts or levels, the exact and short variants, symmetry breaking, and implied subcube tables.
- `scripts/gtable.py`: exact tables. `scripts/show.py` prints them.
- `scripts/layer.py`: the one-cut and two-cut calculators, the calibrations, and the bounds from lower-bound tables.
- `scripts/recursion.py`: recursive upper bounds for g7 and g8.
- `scripts/forest_sa.c`: simulated annealing, used for lower bounds only.
- `data/g4.jsonl`, `data/g5.jsonl`, `data/g6.jsonl`: exact tables, with witnesses and solver logs.
- `data/sa_lower.jsonl`: lower-bound witnesses for Q7 and Q8.
- `data/recursion.json`, `data/q7_runs.txt`: recursion output and the Q7 SAT attempts.
