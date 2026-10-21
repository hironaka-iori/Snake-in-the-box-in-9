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
| `longends` | 300 s caps on ends releases that were UNKNOWN | see the table rows below |
| `holes` | Entries 127-130 are the only bank snakes with undominated vertices (2-3 each). Release every position within distance 2 or 3 of them, 120 s cap | 6 UNSAT (up to 88 positions, 186 free); radius 3 for entries 128 and 130 (253-254 free) UNKNOWN |
| `face7all` | Every Q7 coordinate face of every bank snake (131 x 144 = 18864): release the positions inside it | 18864 UNSAT, at most 109 free vertices |
| `face8all` | Every Q8 face (18) of entries 0, 20, 71, 115, 127, 129, 30 s cap | 108 instances: 62 UNSAT, 46 UNKNOWN (161-211 free) |
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
20-300 s. Regions of 200-250 free vertices, needed for both-end releases
of 60 or more positions per end or for Q8 faces, remain UNKNOWN. A 192-edge
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
python3 $S/summarize2.py
```

`seed186.json` is `{"vertex_sequence": path_vertices}` from
`milestones/19-coordinate-face-repair/data/two-arm-seed186.json`. Because
the caps are wall-clock limits on a shared machine, the UNSAT/UNKNOWN split
near the frontier depends on the load.
