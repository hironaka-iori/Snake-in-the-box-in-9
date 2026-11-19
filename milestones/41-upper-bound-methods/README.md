# Milestone 41: methods that could lower the upper bound by many units

Run of 19 November 2026 on one 4-core machine, beside nothing else. **No bound is claimed.**
Every number below is solver output (CaDiCaL, CP-SAT, Exact), exact-rational LP evidence, or an
explicit validated construction. Nothing here is a Lean result. Bounds are in **edges** unless marked
"vertices". Truth: a(7) = 50, a(8) = 98, and 191 <= a(9) <= 231 (Lean).

## Answer

No method found in this run gives a bound below 229 for Q9. Every relaxation family has a
**provable ceiling**, set by explicit sets that look like snakes locally:

- The cheap families (SDP, Delsarte LP, subcube flag LP) are far above the truth already in Q7 and
  Q8. Their gaps there are 11-12 and 26-28 edges, and in Q9 they give 250-254.
- Every family whose information is confined to Q_k-subcubes is capped at **223 edges for k <= 4**
  and **207 for k = 5**, in Q9. Q_6-locality is the first scale whose fibre ceiling (175) lies below
  the truth.
- The exact global methods (exhaustive search, global SAT) have no ceiling, but their cost grows by a
  factor of 7-26 per two vertices in Q7. They are out of reach for Q9.
- Pseudo-Boolean solving does not unblock the share premises of the 229 route.

**Ranking for "many units".**

1. The w_3 subcube census inside the existing window automata (milestone 22, section 5). It is the
   only lever found that lowers the ceiling of the existing LRAT-to-Lean pipeline: from 223-227 to
   about 209, set by the 208-vertex adversary. Its free window floors, measured here, are no better
   than those of α. Any gain therefore needs the same automaton averaging that has made each unit
   below 233 cost 10-30 times the previous one.
2. Global SAT with lazy cycle cuts. It is exact and LRAT-certifiable with a trivial bridge, but
   exponential.
3. PB / cutting planes on the 229 share premises. No gain was measured, and the route is capped at 226.
4. The flag / subcube-pattern LP.
5. The Delsarte LP.
6. SDP.

## Table

| method | Q7 | Q8 | Q9 | cost | certification for Lean |
|---|---|---|---|---|---|
| (a) SDP / Lasserre / Schrijver, any constraint support < 8 vertices | >= 62 | >= 126 | >= 254 | – | rational dual; pointless |
| (a') the same, support < 14 / < 26 | >= 54 / >= 50 | >= 110 / >= 102 | >= 222 / >= 206 | not solvable at these supports | – |
| (b) Delsarte LP with `s0 >= 0` and `T >= v` (exact simplex) | 62 | 126 | 254 | seconds | rational dual |
| (b') with the Lean chain's `T >= (51/14) v` | – | – | 237 (milestone 22) | | |
| (c) subcube flag LP, Q4 patterns, one path (exact rational dual) | 61 | 124 | 250 | minutes | rational dual over 2,968 patterns |
| (c') ceiling of any Q4-local method | >= 55 | >= 111 | >= 223 | | |
| (c'') ceiling of any Q5-local method | >= 51 | >= 103 | >= 207 | | |
| (c''') fibre ceiling of Q6-local methods | – | >= 87 | >= 175 | | |
| (d) exhaustive search, free-vertex prune (milestone 39 Knuth estimate) | – | 2·10^22 nodes at 100 vertices | 6·10^40 nodes at 222 vertices | infeasible | – |
| (e) PB solver (Exact) on the level-60 share keys | – | – | (229 route, capped at 226) | TIMEOUT at 900 s on 3 of 3 keys | VeriPB would need a new verified checker |
| (f) global SAT with lazy cycle cuts (CaDiCaL) | UNSAT at 58 vertices in 2,268 s; 56 TIMEOUT at 3,600 s | – | – | factor 7-26 per 2 vertices | LRAT, existing checker; bridge trivial |
| (f') w_3 census in window automata | – | – | ceiling about 209 vertices (adversary 208); free floors as weak as α | automaton costs as for α | same pipeline as 233-230 |

The "Q7 / Q8" columns for (c')-(c''') give the ceiling as the size of a validated locally-valid
set minus one, in edges. Rows (a') follow from the same sets. The ceiling of a method is a lower
bound on any bound it can prove, not the value it proves.

## 1. The locality ceiling (rigorous constructions, `scripts/comp_cpsat.py`, `scripts/fake_sa.c`)

Call a set S ⊂ Q_n **Q_k-locally snake-like** if it satisfies three conditions: S induces maximum
degree <= 2, S has at most one path component, and no cycle of S lies in a k-subcube, i.e. every
cycle uses more than k coordinate directions.

Every condition that inspects S only through its intersections with k-subcubes is satisfied by
such sets, apart from the endpoint terms. This covers subcube census windows, flag LPs over k-subcube
types, and the layering by facets of dimension k. The endpoint terms are repaired by deleting one
vertex of a cycle, as in milestone 39.

Fibre sets: take disjoint induced cycles A, B ⊂ Q_m, each using all m directions, and put
`S = {(x,y) ∈ Q_m × Q_{n-m} : x ∈ A if |y| even, x ∈ B if |y| odd}`. Adjacent fibres carry disjoint
sets, so S is a union of 2^{n-m} induced cycles of span m, and `|S| = 2^{n-m-1}(|A|+|B|)`. Write
P(m) for the largest such |A|+|B|. CP-SAT found and validated:

| m | P(m) | how |
|---|---|---|
| 5 | 28 (14 + 14) | OPTIMAL |
| 6 | 52 (26 + 26) | milestone 11 |
| 7 | >= 88 (44 + 44) | FEASIBLE after 1,800 s, `data/pair_m7.txt` |

Hence, for n = 7, 8, 9:

- Q4-local: 56, 112, 224 vertices.
- Q5-local: 52, 104, 208 vertices.
- Q6-local: 88 vertices for n = 8 (m = 7, fibre over Q1) and 176 for n = 9.

Annealing (`data/h_table_raw.txt`) reproduces the Q7 values: 56 vertices at k = 4, 52 at k = 5, and
51 (the truth) at k = 6. At n >= 8 the annealer falls below the constructions.

Consequences:

- **Below 222, a method must see cycles of span 5 (the 14-cycles of Q5).** Plain windows of at
  most 7 centres do not, and neither do any constraints on fewer than 14 vertices. Windows whose
  CNF contains a full radius-3 ball do see them (milestone 11's caveat).
- **Below 206, a method must see cycles of span 6.** No radius-3 ball contains a 26-cycle of the
  208-vertex set.
- In Q7 the Q5-local ceiling is 51 edges, one above the truth. The gap between local and global
  closes fast with the ratio k/n.
- Q6-local fibre sets in Q9 have at most about 176 vertices, below the truth. Whether non-fibre
  Q6-locally snake-like sets beat 192 vertices is open. A CP-SAT search for one long cycle of span
  >= 8 plus a path in Q8 is in `data/q8_cycle7_path.txt`.

## 2. LP and SDP numbers

- `scripts/delsarte_run.py` uses the exact simplex of milestone 22. Delsarte alone and Delsarte with
  `s0 >= 0` both allow v = 2^{n-1} + 1 for n = 6..9. Adding `T >= v` (the singleton lemma) gives
  `2^{n-1} - 2` edges: 30, 62, 126, 254.
- `scripts/flaglp_c1.py` is the hypergeometric Q4-pattern LP of milestone 32 at c = 1 path, with
  exact rational dual certificates (`data/flaglp_c1.jsonl`):
  - Q7: 62.19 vertices, i.e. 61 edges;
  - Q8: 125.37 vertices, i.e. 124 edges;
  - Q9: 251.81 vertices, i.e. 250 edges.
- SDP of any level whose constraints have support < d vertices is bounded below by the sets above,
  with d = 8, 14, 26 (milestone 39's `sdp_ceiling.py`). A Schrijver or Lasserre-2 hierarchy has
  support at most 4, so it is capped at 254 in Q9, 126 in Q8 and 62 in Q7. It was therefore not
  implemented.

## 3. Exact global methods

### Global SAT (`scripts/snake_sat.py`, `data/sat_global.txt`)

The encoding has these clauses:
- max degree 2;
- no isolated selected vertex;
- at most two degree-one vertices;
- at least V vertices;
- the symmetry fix "0, e0, e1 selected".

Cycle cuts are added lazily. Every clause holds for every snake, so an UNSAT answer would be an
LRAT-certifiable refutation. The Lean bridge is much simpler than the window bridges.

| n | V (vertices) | result | seconds |
|---|---|---|---|
| 6 | 28 | UNSAT | 34 (18 with direction sorting) |
| 7 | 64 | UNSAT | 6 |
| 7 | 62 | UNSAT | 12.5 |
| 7 | 60 | UNSAT | 86 |
| 7 | 58 | UNSAT | 2,268 |
| 7 | 56 | TIMEOUT | 3,600 |

The cost grows by a factor of 7 to 26 per 2 vertices. Proving a(7) <= 50 (V = 52) extrapolates to
10^6 s or more. Q9 at 220 lies as far below Huang (256) as Q7 at 55 lies below 64, and has 4 times
the vertices. Direction-count sorting helped at n = 6 and not at n = 7. Huang capacity constraints
on subcubes made the run slower.

CP-SAT with an exact `AddCircuit` model (`scripts/snake_cpsat.py`) is much weaker. It needs 414 s
just to find a 27-vertex snake in Q6.

### Exhaustive search

Milestone 39 measured the free-vertex-prune DFS: 2·10^22 nodes for Q8 at 100 vertices and 6·10^40
for Q9 at 222. The estimate is almost independent of the target, 8·10^38 at 232. Pruning by the
proved local exclusions acts only deep in the tree. It was not re-measured here, to avoid
duplicating milestone 39.

## 4. Pseudo-Boolean certificates for the 229 share premises (`scripts/pb_share.py`)

The setup is the same CNF as milestone 38's `AltShare`: window, ball, e0 and degree totalizers,
share clauses. Only the counter over the u literals is replaced by one native linear constraint
`Σ u <= 59`, which is solved by the cutting-planes solver Exact 2.2.1 with lazy cycle cuts.

- Consistency check on shape `0,1,2,0,3,4,2,5` at level 30: UNSAT in 0.7 s, as CaDiCaL.
- The three hard level-60 keys (`data/pb_share60.jsonl`) all hit TIMEOUT at 900 s:
  - `0,1,2,3,4,0,1,5`, which CaDiCaL solves in 170-258 s;
  - `0,1,2,3,4,1,2,5`, which CaDiCaL leaves at TIMEOUT at 900 s;
  - `0,1,2,3,4,5,2,4`, which CaDiCaL solves in 557 s with lex-leader clauses.

The difficulty is not the cardinality reasoning on the final sum. It sits in the per-corner share
definitions, whose divisions by degree are still clauses. A PB model of `floor(M e0/d)` would need
products. Even if PB worked, a VeriPB proof would need a new verified checker in Lean, and the
uniform-share route is capped at 226 (milestone 38).

## 5. The w_3 census in windows (`scripts/w3win.py`, `data/w3win_r3.jsonl`)

`Σ_{x∈S} w_3(x) <= N_3 = 5376` with `w_3(x) = Σ_{3-cubes Q ∋ x} 1/|Q ∩ S|`. Its real-snake slack is
0.3-0.6 %, against 9 % for the square census. The 208- and 224-vertex adversaries give floors of
209.9 and 225.3 vertices (milestone 22).

Here is the minimum of the mean w_3 over the centres of a free window (radius 3, CP-SAT, lazy cycle
cuts, 240 s per shape). The "found" value is an achievable window, so it is an upper bound on the
floor; the "bound" is CP-SAT's lower bound.

| centres | shape | found | bound | `5376/found` vertices |
|---|---|---|---|---|
| 1 | `0,1` | 21.00 (optimal) | 21.00 | 256 |
| 2 | `0,1,2` | 22.03 | 20.73 | 244 |
| 4 | `0,1,2,3,0` | 22.87 | 20.99 | 235 |
| 4 | `0,1,2,0,3` | 23.88 | 20.88 | – |
| 5 | `0,1,2,0,3,4` | 24.29 | 21.27 | – |

All other shapes hit TIMEOUT. Already at 2 and 4 centres, windows exist whose mean w_3 corresponds
to 244 and 235 vertices. A w_3 automaton therefore starts from the same position as the α automata
did, a free floor at Huang's level. It would have to climb by averaging over long windows: at least
24.3 is needed for 220 edges and 23.2 for 230. This is the same cost structure that led to the
33,628 exclusions of 230.

The census removes the s0 slack, and that is why its *ceiling* is lower (about 209). It does not
make the *local refutations* cheaper.

## What would be needed for a bound below 220

The lever must be a method whose local information spans Q5 or Q6 configurations exactly, or a
genuinely global argument. The measurements say:

- **Exact local data at Q5 or Q6 scale** is the minimum. In Q7 the Q5-locality ceiling is already
  the truth plus 1. So an exact local-to-global principle at that scale would be close to optimal
  in Q7 and Q8. The open question is a *tractable relaxation* of "S ∩ Q is a forest for every
  6-subcube Q". The subcube flag LP has a relaxation gap of 11 or more in Q7 even at k = 4
  (milestone 32).
- **Cube-and-conquer global SAT** is the only exact certifiable route. Its Q7 scaling must improve
  by orders of magnitude before Q9 is thinkable. Directions that could do that: much stronger
  symmetry breaking (canonical augmentation inside the solver, as in Östergård-Pettersson), or
  layering cubes. Layering cubes split on the direction counts, and a small count gives `v <= 198`
  at once by milestone 29.

## Files

- `scripts/comp_cpsat.py`: fibre pairs and locally snake-like sets (CP-SAT), with an independent
  validator.
- `scripts/fake_sa.c`: milestone 32's annealer. `scripts/run_h.sh` runs it over the grid.
- `scripts/delsarte_run.py`, `scripts/flaglp_c1.py`: the LP numbers.
- `scripts/snake_sat.py`, `scripts/run_satq7.sh`: global SAT. `scripts/snake_cpsat.py`: the
  CP-SAT circuit model.
- `scripts/pb_share.py`, `scripts/run_pb.sh`, `scripts/cmp_cnf.py`: PB versus CaDiCaL on the share
  keys.
- `scripts/w3win.py`: w_k window floors.
- `data/`: raw outputs. `w3win_r4_partial.jsonl` holds the radius-4 attempt, which hit TIMEOUT on
  most shapes.

Requirements: `pip install ortools highspy exact python-sat`. The CaDiCaL binary is expected at
`/usr/local/bin/cadical` (milestone 38's `binsolve.py`).
