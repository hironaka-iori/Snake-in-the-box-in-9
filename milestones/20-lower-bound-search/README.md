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
