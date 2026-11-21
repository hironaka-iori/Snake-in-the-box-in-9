# Fleet search for a 192-edge snake in Q9: helper instructions

Each helper machine (4 cores, about 14 GB) runs ONE variant with its own machine index M (1, 2, 3, ...; distinct on every machine, even across variants). Runs unattended forever until killed; memory well under 1 GB.
Requirements: gcc, python3; the `window` variant also needs `ortools` (the script pip-installs it if missing).

## Launch lines (run from the repository root)
```
nohup milestones/40-lower-bound-search/src/fleet.sh sym    M > fleet_sym_M.out    2>&1 &
nohup milestones/40-lower-bound-search/src/fleet.sh q8     M > fleet_q8_M.out     2>&1 &
nohup milestones/40-lower-bound-search/src/fleet.sh window M > fleet_window_M.out 2>&1 &
nohup milestones/40-lower-bound-search/src/fleet.sh plain  M > fleet_plain_M.out  2>&1 &
```
Optional third argument: number of parallel workers (default 4).

## Variants
- `sym`: symmetry-restricted annealing (`src/sym.c`): each 10-min run picks a random involution sigma of Q9 (coordinate transpositions plus a flip mask) that admits a centre, and anneals over sigma-invariant snakepits with cube-surgery moves. 5-min tests reached 178 edges; whether a symmetric 192 exists is unknown.
- `q8`: surgery annealing (`src/surgery.c`) started from two long Q8 snakes (95-98 edges, 60 s by the same annealer) in the facets x8=0 and x8=1 under a random cube automorphism (`src/q8prime.py`). 188 edges in a 4-min test.
- `window`: exact CP-SAT window repair (`src/window_repair.py`) of the 131 bank 191-snakes: frees 60-130 consecutive vertices and maximises the replacement exactly, 600 s per solve.
- `plain`: baseline surgery annealing (10-min fresh restarts).

## Output
- Logs: `milestones/40-lower-bound-search/logs/fleet/VARIANT_M/` (BEST lines carry full vertex lists).
- After every run any snake with >= 192 edges is re-validated by the independent checker `src/check.py`; only if it passes is it appended to `milestones/40-lower-bound-search/logs/fleet/FOUND192.txt` and printed to the nohup output with the full vertex list.
- Helpers cannot push to research/*: send any FOUND192 entry (whole vertex line) to the coordinating session by message.

## Stopping
Kill by PID only: `pgrep -f fleet.sh`, and children `pgrep -f "bin/sym|bin/surgery|window_repair"`, then `kill <PID>...`.
