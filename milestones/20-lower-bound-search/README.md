# Lower-bound search: SAT large-neighbourhood repair of the bank

Checkpoint: 21 October 2026. Target: a snake in Q9 with at least 192 edges.
**No snake longer than 191 edges was found.** The best length reached is 191,
and every 191-edge snake the search produced is equivalent to an entry of the
131-entry bank (`work/bank9.json`). No Lean witness module was added, because
there is no new witness.

## Method

`scripts/lns.py` repairs a snake P inside a released set R of path positions.
Vertices of P outside R are kept. Any vertex adjacent to a kept vertex that
already has two kept neighbours is excluded. All other vertices are free
Boolean variables. The CNF requires:

- selected degree 1 or 2 for every selected vertex;
- exactly two degree-1 vertices, so both endpoints may move;
- at least `target` selected vertices;
- no fully selected coordinate square.

Such a graph is one path plus cycles. A cycle component C is removed lazily by
the clause "not all of C is selected". This clause is valid because an induced
path contains no cycle; it is the cut used in milestones 14 and 17. The solver
is Glucose 4.2 through PySAT 1.9, with a wall-clock interrupt. CaDiCaL in PySAT
cannot be interrupted. Every SAT answer is checked again by `is_snake`, which
tests distinctness, adjacency of consecutive vertices and distance at least 2
for all other pairs. Releasing a set of positions that contains a smaller
released set can only add solutions, so one large window covers all of its
sub-windows.

Releasing a window of interior positions, with both attachments kept, fixes
the parity of the replacement (DfsParity). Such a window therefore needs +2
vertices. Windows that touch an end, and the region types used in the random
searches, let the endpoints move.

Released windows stay tractable because the bank snakes dominate the cube: in
127 of 131 entries every vertex is on the snake or adjacent to it. An 80-position
window leaves at most 142 free vertices. The solver settles these in about 0.7 s
on average. Free sets of about 160 or more were usually UNKNOWN within 10 to 30 s.

## Experiments (one core, `nice -n 19`)

| Run | What | Result |
|---|---|---|
| `sweep80` | All 131 bank snakes, every window of 80 consecutive positions starting at 0, 8, ..., 112 (ends included), target 193 vertices, 10 s cap | 1965 windows: 1939 UNSAT, 26 UNKNOWN (bank entries 3, 4, 20-24, 115, 127-130), 0 SAT |
| `walk1` | Plateau walk from entry 129. Random region (window 40-90, two windows, or Hamming ball of radius 3-4). First ask for 193 vertices. If refuted, move to a different 192-vertex filling. | 125 steps, 0 improvements, 42 neutral moves, 0 new 191-edge classes |
| `anneal2`, `anneal3` | Same regions. Uphill (len+1) first, then a neutral or downhill (len-1) different filling | 428 steps. The state stayed at 190-191 edges. 381 visits to 191-edge snakes covered 55 bank classes, all of them in the bank |
| `ils4` | Iterated local search: 6 forced exact downhill kicks (to 185 edges), then climb with uphill or neutral moves until 40 steps pass without progress | 15 episodes. Every climb returned to exactly 191 edges, each time a bank class |
| `ils5` | Same with 16 kicks and no reset | 1 episode: fell to 175 and climbed only to 182 (pilot, stopped) |
| `ils6` | 10 kicks (to 181 edges), regions of 60-110 positions, patience 50 | 8 episodes: 7 climbed back to 191, each time a bank class; 1 stalled at 184 |

Across the anneal and ILS runs, the climbs reached 67 distinct bank
classes and no 191-edge snake outside the bank. `data/summary.json` gives the
exact counts per run.

## Interpretation

These are restricted solver results and not proofs. Within the neighbourhoods
tried, the 131 bank classes behave like a closed plateau: the moves connect
them to each other and to shorter snakes, and every climb from snakes 6-10
edges shorter returns to a bank class. This is consistent with milestones 18
and 19, where neutral repairs recovered bank entries and every 6-dimensional
face repair of entry 129 failed. UNSAT on a window excludes 192-edge snakes
that agree with that bank snake outside the window. These exclusions have no
proof certificates. The LNS approach probably needs a starting configuration
outside the bank basin, for example the milestone 19 two-arm 186-edge seed or
a layer construction. It may also need regions with roughly 160-250 free
vertices, where the present CNF gives UNKNOWN. A stronger encoding, for
example with symmetry breaking or redundant cuts on 6-cycles, would be needed
for those regions.

## Files and reproduction

- `scripts/lns.py`: model, lazy cycle cuts and independent snake check.
- `scripts/drive.py`: the `sweep`, `walk`, `anneal` and `ils` drivers.
- `scripts/summarize.py`: rebuilds `data/summary.json` from the logs.
- `scripts/gen_lean.py`: writes a witness module modelled on the witness in
  `work/final_lean/Snake9.lean`. It was not used, because no new witness was found.
- `data/*.jsonl.gz`: per-instance logs; `data/summary.json`.

```sh
nice -n 19 python3 milestones/20-lower-bound-search/scripts/drive.py sweep --widths 80 --step 8 --tl 10 --log sweep80.jsonl --outdir out
nice -n 19 python3 milestones/20-lower-bound-search/scripts/drive.py ils --seed 4 --start 60 --hours 2.2 --tl 8 --wmin 50 --wmax 100 --kick 6 --patience 40 --reset 189 --log ils4.jsonl --outdir out
python3 milestones/20-lower-bound-search/scripts/summarize.py
```

The random runs depend on wall-clock interrupts, so their exact trajectories
do not reproduce.

## Round 2: stronger encoding, larger and two-sided neighbourhoods

Checkpoint: 21 October 2026, about 3.5 hours on one core at `nice -n 19`.
**No snake longer than 191 edges was found.** No new witness, so no Lean
module was added. All results below are restricted solver results without
proof certificates.

### Stronger model (`scripts/lns2.py`)

`Model2` keeps the round-1 search space (kept vertices fixed, selected degree
1 or 2, exactly two endpoints, at least `target` selected, lazy cycle cuts)
and adds constraints that every induced path of Q9 satisfies:

- colour balance: the two colour classes of a path differ by at most one,
  encoded by two full totalizers and linking clauses;
- hexagon cuts: no induced 6-cycle (every 6-cycle of Q9 lies in a Q3);
- subcube capacity: the trace of a snake on a Q4 is an induced linear
  forest, so at most 8 of its 16 vertices are selected. `scripts/capq.py`
  gives the maxima 5, 8, 16, 32 for Q3 to Q6, by enumeration for Q3 and Q4
  and by SAT with cycle cuts for Q5 and Q6. A Q5 cap of 16 is optional; it
  slowed the solver on the instance tried.

The solver is CaDiCaL 1.9.5 through PySAT, run in conflict-budget chunks so
that a wall-clock cap applies (its interrupt does not work from a thread).
Every SAT answer is checked again by `lns.is_snake`. Controls: for target
192, the original filling is found on several windows. On bank entry 129,
window 72-151 (142 free vertices, UNKNOWN in round 1), Glucose stays UNKNOWN
for target 192 at 60 s. For target 193, CaDiCaL proves UNSAT in 53-84 s
with or without the added cuts. The main gain is the solver. Colour balance
gave the fastest run, but timings under a shared load are noisy.

### Experiments

| Run (`data/r2-*.jsonl.gz`) | What | Result |
|---|---|---|
| `unknown` | The 26 round-1 UNKNOWN windows (80 positions, 127-142 free), target 193, 120 s cap | 26 UNSAT (1.2-116 s). With round 1, all 1965 windows of `sweep80` are now UNSAT |
| `endsadapt` | Both ends at once: release positions [0,T/2) and [n-T/2,n), T = 110, 120, ..., stop at the first UNKNOWN; 20 s cap; all 131 entries | 240 instances, 109 UNSAT, 131 UNKNOWN. Largest UNSAT release: T = 120 for 25 entries, T = 110 for 59, none for 47. Largest UNSAT free set 188; smallest UNKNOWN 168 |
| `pilot` | Entry 0, ends 40:40 to 60:60 and asymmetric 30:70, 70:30, 20:90 | UNSAT up to 55:55 and 30:70/70:30 (150-160 free); 60:60 (199 free) and 20:90 (186 free) UNKNOWN at 120-150 s. In a separate bench, 60:60 was UNSAT in 234 s |
| `longends` | 300 s caps on three UNKNOWN both-end releases: entry 115 at 55:55 (184 free), 129 at 55:55 (195), 20 at 60:60 (200) | 3 UNKNOWN |
| `holes` | Entries 127-130 are the only bank snakes with undominated vertices (2-3 each). Release every position within distance 2 or 3 of them, 120 s cap | 6 UNSAT (up to 88 positions, 186 free); radius 3 for entries 128 and 130 (253-254 free) UNKNOWN |
| `face7all` | Every Q7 coordinate face of every bank snake (131 x 144 = 18864): release the positions inside it | 18864 UNSAT, at most 109 free vertices |
| `face8all` | Every Q8 face (18) of entries 0, 20, 71, 115, 127, 129, 30 s cap | 108 instances: 62 UNSAT (up to 238 free), 46 UNKNOWN (161 or more free) |
| `grow7` | LNS from the milestone 19 off-bank 186-edge seed: random windows, two windows, both ends, Hamming balls; uphill (L+1) or a different equal-length filling | 186 to 191 edges in 14 steps; all 191-edge states were bank entries 127-130; stopped after 27 steps |

The coordinate faces used in milestone 19 are small neighbourhoods for bank
snakes: the fixed part outside a Q7 face dominates most of the face. Releases
by path position, in particular at both ends, give much larger free sets.

### Interpretation

The off-bank 186-edge seed is not off the basin: it shares 142 vertices with
entry 129, and the first climb returns to entries 127-130. The bank has no
192-edge extension within any 80-position window, both-end releases of 110
positions, any Q7 face, or the undominated-vertex balls of radius 2. With
the present encoding, the solver frontier is about 180-200 free vertices at
20-300 s; some Q8-face instances with up to 238 free vertices still close. Regions of 200-250 free vertices, needed for both-end releases
of 60 or more positions per end or for many Q8 faces, remain UNKNOWN. A 192-edge
snake, if one exists, appears to need a global structure different from
the bank rather than a local repair of it.

### Reproduction

```sh
S=milestones/20-lower-bound-search/scripts
nice -n 19 python3 $S/drive2.py unknown   --tl 120 --log unknown.jsonl --outdir out
nice -n 19 python3 $S/drive2.py endsadapt --tl 20 --fracs 0.5 --t0 110 --log endsadapt.jsonl --outdir out
nice -n 19 python3 $S/drive2.py holes     --radii 2 3 --tl 120 --log holes.jsonl --outdir out
nice -n 19 python3 $S/drive2.py faceall   --dim 7 --tl 60 --log face7all.jsonl --outdir out
nice -n 19 python3 $S/drive2.py faceall   --dim 8 --tl 30 --banks 0 20 71 115 127 129 --log face8all.jsonl --outdir out
nice -n 19 python3 $S/drive2.py grow --start-file seed186.json --seed 7 --hours 0.8 --tl 30 --log grow7.jsonl --outdir out
python3 $S/summarize2.py   # data/round2-summary.json
```

`seed186.json` is `{"vertex_sequence": path_vertices}` from
`milestones/19-coordinate-face-repair/data/two-arm-seed186.json`. Because
the caps are wall-clock limits on a shared machine, the UNSAT/UNKNOWN split
near the frontier depends on the load.

## Round 3: global search for reversal-symmetric snakes

Checkpoint: 21 October 2026, about 4.5 hours on one core at `nice -n 19`.
**No snake longer than 191 edges was found.** The longest symmetric snake
found has 178 edges, and the longest snake grown from it has 183 edges. No
Lean module was added. All UNSAT/UNKNOWN statements below are restricted
solver results without proof certificates.

### Choice of method

Milestone 02 and `work/joint_layer_search.py` already searched joins of two
Q8 paths across one coordinate (option b). Milestones 12-18 tried defect
annealing, cycle-component merging and Q5-cell products. Round 3 therefore
tests option (a), a global family that none of these touches: snakes that an
automorphism of Q9 maps onto themselves. No entry of the bank has this
property: for all 131 entries, no coordinate permutation maps the transition
sequence onto its reverse. Every symmetric snake therefore lies outside
the bank. The quotient model has half as many variables, so a release
of W orbit positions frees about 2W path positions.

### Which symmetries are possible (`scripts/sym3.py`)

Let g be an automorphism with g(P) = P for a snake P that uses all nine
directions. Then g acts on P as a path automorphism, so it is either the
identity or the reversal. P spans the cube affinely. Hence g = id, or g
reverses P and g² = id. **Order 4 is impossible**, and only involutions
g(x) = π(x) ⊕ c can occur. Up to conjugation, the class of g is (k, w): π
has k transpositions, c is zero on the transposed pairs and has weight w on
the fixed coordinates.

- If P has an odd number of vertices, its middle vertex is fixed, so w = 0.
- If P has an even number of vertices, g swaps the two ends of the middle
  edge, so g(v) = v ⊕ e_f for some v. This forces w = 1.
- Classes with w ≥ 2 admit no symmetric snake. In class (0, 1), g is a
  translation, which would make the two path ends adjacent.

Thus 192, 194 and 196 edges need a class (k, 0), and 193 and 195 edges
need a class (k, 1), for k = 1..4. That gives eight classes in Q9. A
fixed-point-free g allows only odd edge counts.

The model has one Boolean per g-orbit, lifted to all vertices with
multiplicities. Every selected vertex has selected degree 1 or 2. There is
exactly one orbit of endpoints. Coordinate squares and hexagons are cut,
and every Q4 holds at most 8 selected vertices. The vertex count is exact.
There is exactly one selected fixed vertex (w = 0), or exactly one selected
orbit {v, g(v)} that is an edge (w = 1). Cycle components are cut lazily.
Symmetry breaking by the centralizer of g puts the middle vertex at 0 (w = 0)
or the middle edge at {0, e_f} (w = 1). Solver: CaDiCaL 1.9.5 in
conflict-budget chunks, as in round 2. Every snake is checked by
`is_snake` and for g-invariance.

**Validation.** In Q5 and Q6, the maximum symmetric length per class from
SAT equals the maximum from brute-force DFS over all snakes:

| | (1,0) | (1,1) | (2,0) | (2,1) | (3,0) |
|---|---|---|---|---|---|
| Q5 | 10 | 11 | 12 | 11 | - |
| Q6 | 16 | 17 | 22 | 23 | 26 |

Symmetric snakes reach a(6) = 26 but not a(5) = 13. In Q7, the best is
48 edges for class (3,0), where 50 is UNSAT. Class (2,1) gives 47, with 49
UNSAT. Class (1,0) is UNSAT already at 30 edges, and class (1,1) at 45.
So in Q7 the best symmetric snakes are 2 edges below a(7) = 50.

### Experiments (`data/r3-*.jsonl.gz`, `data/round3-summary.json`)

| Run | What | Result |
|---|---|---|
| `q9a`, `q9b` | Q9 from scratch, ladders with a 90-120 s cap | (4,0) and (3,0): 160 SAT (12-32 s), 170 UNKNOWN. (4,1) and (3,1): 161 SAT. (2,0): 140 SAT, 150 UNKNOWN. (2,1): 151 UNKNOWN. (1,0): 140 UNSAT in 3 s |
| `q8b`, `q8lns`, `q8cal` | Q8 calibration | (4,0) and (3,0): 90 SAT in at most 34 s. Symmetric LNS: 90 -> 94 by step 3, then 219 steps without progress. Direct (4,0) 96 and (3,1) 95, 97: UNKNOWN at 300-600 s |
| `q9lns-k4a`, `-k4w0b` | Symmetric LNS (`scripts/symlns.py`), class (4,0), from 160 | 160 -> 178 in 49 steps. Then 300+ steps at 178 (neutral moves, kicks to 176, climbs back) |
| `q9lns-k4w1` | class (4,1) from 161 | best 171 |
| `q9lns-k3w0` | class (3,0) from 160 | best 168 |
| `q9lns-k3w1` | class (3,1) from 161 | best 173 |
| `grow11` | Round-2 asymmetric LNS (`drive2.py grow`) from the 178-edge (4,0) snake | 178 -> 183 in 51 steps, then 228 steps at 183 (279 steps, 45 min) |

Symmetric LNS (`scripts/symlns.py`) releases a set of half-positions
r(i) = min(i, len-1-i). It passes the kept orbits as assumptions to one
persistent model per length, so learned clauses and cycle cuts carry over
between steps. Each step first asks for +2 edges (one more orbit). If that
fails, it asks for a different filling of the same length (neutral move).
After 30-40 steps without progress, it asks for a different filling 2 edges
shorter (kick). Released sets are windows, two windows, both ends, or
Hamming balls of radius 3-4. Their size adapts: +2 after an UNSAT up-move
and -3 after an UNKNOWN. The usual size settled at 45-60 of the about 90
half-positions, that is 90-120 path positions, with 30 s caps.

The best snakes are in `data/r3-best/`. Each passes `lns.is_snake`, and
the symmetric ones are g-invariant. All are far below 191. The 178-, 171-
and 183-edge snakes dominate all or all but one vertex of Q9, like the
bank snakes.

### Interpretation

The symmetric family is a poor place to look for a 192-edge snake:

1. In Q5-Q7 the symmetric maximum is 0-2 edges below a(n).
2. In Q9 the four strongest classes stalled at 168-178 edges. Release
   regions of 90-120 path positions were mostly refuted within seconds.
3. Classes (1, w) are capped far lower. Classes (2, w) were already UNKNOWN
   at 150-151 edges from scratch.

Leaving the symmetry and repairing the 178-edge snake with the round-2
encoding gained only 5 edges, and stopped at 183. So a 192-edge snake, if
one exists, is unlikely to be a symmetric snake within 20 edges of a
symmetric LNS optimum. The Q8 calibration is inconclusive (94 found, 95-97
UNKNOWN), so these stalls do not prove a ceiling. A complete answer for
one class would need an exhaustive quotient search, for example proving
(4,0) UNSAT at 192 edges. At 170 edges the solver is already UNKNOWN after
2 minutes.

### Reproduction

```sh
S=milestones/20-lower-bound-search/scripts
nice -n 19 python3 $S/drive3.py --n 9 --ks 4 3 --edges 160 170 --tl 120 --log q9a.jsonl --outdir out --stop-unknown
nice -n 19 python3 $S/symlns.py --n 9 --k 4 --start out/sym-n9-k4-e160.json --hours 0.75 --tl 30 --wmin 20 --wmax 90 --patience 30 --log k4.jsonl --outdir out
nice -n 19 python3 $S/drive2.py grow --start-file milestones/20-lower-bound-search/data/r3-best/sym-k4w0-e178.json --seed 11 --hours 0.75 --tl 30 --log grow11.jsonl --outdir out
python3 $S/summarize3.py   # data/round3-summary.json
```

The walks depend on wall-clock caps on a shared machine, so their
trajectories do not reproduce exactly. In the first (4,0) run (`q9lns-k4a`),
the region size grew only after failed neutral moves. The adaptation was
then changed to the rule above.
