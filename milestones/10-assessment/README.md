# Distance-to-answer assessment

Checkpoint: 17 October 2026. Nothing here changes the checked interval 191 <= a(9) <= 245. Every result below is a computation or a literature check, not a Lean theorem. Each finding is labelled with its evidence level.

## Main findings

| Finding | Evidence |
|---|---|
| On a path, W = v-2 exactly, so the incidence identity becomes E + 2T + 70v = 18428 (E counts empty squares from corners) | Python check on bank snakes |
| Any length-uniform density bound T >= c*v proves at most about 208-210 edges, because a real bank snake has T/v = 8.5 | Computation |
| Radius-3 window survey: 12 alpha triples infeasible in both window shapes; exact DP bounds 245 (proved set), 244 (+223), 242 (all 12) | CP-SAT, uncertified |
| 242 is the exact ceiling of any 3-window argument: (2,3,3), (2,4,2), (3,2,4) occur in genuine checked snakes | Explicit snakes, Python-checked |
| 5-window radius-3 exclusions suggest about 238-239 | CP-SAT loop snapshot, uncertified |
| Realized-window ceilings: 4-, 5-, 6-vertex windows cannot prove better than 227, 223, 217 | Computation |
| Bank structure: the 4 least-used coordinates carry 19-32 transitions; every Q5 fiber holds at most 14 = a(5)+1 vertices; the least-used coordinate is used 1-4 times | Python |
| Fixed-outer-word inner CP-SAT model recovers 192-vertex snakes with hints; UNKNOWN in 600 s without hints | CP-SAT, all pairs checked |
| Knuth-estimator search tree sizes for the symmetry-broken DFS: Q6 26,852 (exact), Q7 1.6e10, Q8 5.7e21, Q9 6.9e44 | Estimate; a reviewer judged the Q9 figure pessimistic for the problem itself |
| Regrowth cost grows far faster than 10-15x per 8 freed vertices beyond KEEP=112 | Measured totals and estimates |
| Published snake upper bound for Q9 is 255 (Huang); sharper classical bounds such as Solov'jeva's 248 apply to coils only. The repo's 245 appears to be the best explicit snake bound | Literature search; Emelyanov-Lukito 2000 and Snevily 1994 not read |

## Files

- `scripts/session/`, `data/session/`: window survey, potential and DP bounds, fiber analysis and the fiber CP-SAT prototype.
- `scripts/workflow/`, `data/workflow/`: independent agent reruns, window ceilings, 5-window cut loop, Delsarte LP probes, Knuth estimators, SAT scaling runs and regrowth cost measurements.

The scripts were written in a temporary session directory and still contain its absolute paths. Adjust those paths before rerunning. Solver runs used OR-Tools 9.15.6755 and python-sat 1.9.dev16.

## Documentation note

`milestones/08-exhaustive-search/README.md` and `lean_completion.md` still describe KEEP=112 as uncertified, whereas `work/lean112/RESULTS.md` records its completion on 17 October 2026.
