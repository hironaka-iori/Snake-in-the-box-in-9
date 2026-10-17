# Window exclusions and stronger aggregate bounds

Checkpoint: 17 October 2026.

**Status.** Two new *conditional* upper bounds are proved in Lean: at most **242 edges**, and at most **241 edges** with one extra premise. The premises are exclusions of certain singleton-count patterns on three or four consecutive internal path vertices. Each premise has a **DRAT-checked** unsatisfiability certificate for an explicit local CNF. None is a Lean theorem yet. The unconditional checked interval therefore remains **191 <= a(9) <= 245**.

## What this milestone adds

The incidence identity gives `T + 2*s0 = 9214 - 35*v`. Here `T` is the total singleton-square count, `s0` the number of empty squares, and `v` the number of vertices. The existing proof bounds `T` from below by a potential argument on the count sequence `alpha_0, ..., alpha_{v-1}` along the path. Its worst sequences repeat `2,2,3`, with average `7/3`. Because a universal bound `alpha >= 2` is false, any improvement must restrict *how often* low counts occur.

This milestone asks which count windows a local ball model allows. It then derives the best aggregate inequality those windows support.

1. **Local model** (`scripts/wincert.py`). Fix consecutive path vertices `x_0..x_{k+1}` with internal centers `x_1..x_k` and prescribed counts. The model is the radius-three Hamming ball around the centers. Every clause is a necessary condition on `S ∩ B` for an induced path `S`:
   - the window vertices are selected;
   - every ball vertex has at most two selected neighbours;
   - a vertex whose whole neighbourhood lies in the ball has one or two, and one means endpoint;
   - at most two endpoints occur;
   - each center's count equals its prescribed value: count the absent opposite corners over the 21 coordinate pairs avoiding its path directions;
   - there are no 4-cycles, no 6-cycles inside 3-faces, and no cycle cuts found lazily.

   Up to coordinate relabelling and reversal, there are two 3-center window shapes, with directions `0,1,2,0` and `0,1,2,3`. There are three 4-center shapes: `0,1,2,0,3`, `0,1,2,3,0`, and `0,1,2,3,4`.
2. **Survey** (`scripts/survey.py`, `data/survey_*.json`). Every 3-center count triple with entries 1..6 was decided in both shapes, and a targeted set of 4-center windows in all three shapes. Of the 216 triples, 144 are feasible in some shape. The minimum mean count over sequences whose consecutive triples are feasible is **14/5**. The worst cycle is `2,3,3,2,4`. The current Lean premises give **7/3**.
3. **Ceiling with four windows.** A window `x_0..x_5` with counts `(2,4,2,3)` or `(3,2,4,2)` is infeasible in all three 4-center shapes. Adding only this exclusion raises the minimum mean to **3**. Every untested 4-window was counted as feasible, so this is a valid lower bound.
4. **Certificates** (`scripts/certify.py`, `certificates/`, `data/certificates.json`). There are 22 cases:
   - 16 for the triples, in both shapes and both orientations: `(2,2,3)`, `(2,2,4)`, `(2,3,2)`, `(3,2,3)`, and `(4,1,c)` with `4<=c<=6`;
   - 6 for `(2,4,2,3)` and its reversal.

   CaDiCaL produced each DRUP proof. The repository's vendored `drat-trim` verified every one (`work/keep96/vendor/drat-trim`, source hash checked). The gzipped CNF and proof files are about 16 MB.
5. **Positive controls** (`scripts/controls.py`, `data/controls.json`). There are 532 windows: from the 131 bank snakes, the 191-edge witness, and the 137-edge count-one counterexample, including counts 1 and 3. Each satisfies every clause of its CNF with its true counts and selection.
6. **Lean.**
   - `work/spectral/stronger/WindowPotential242.lean` and `WindowPotential241.lean` use core Lean only. They prove the sequence inequalities `14*n <= 5*sum + 12` and `3*n <= sum + 4` by potentials checked by kernel evaluation of finite tables.
   - `AggregateWindowConditional.lean` uses mathlib and combines them with the existing incidence identity. It proves `upper_242_of_certified_windows` and `upper_241_of_certified_windows` for the original `Snake9.Snake`.
   - The (2,2,2) case is discharged by the existing theorem, and the count-one neighbour bound and endpoint bound are reused. Only the listed window premises remain as hypotheses.

| Assumed window exclusions | Minimum mean | Bound |
|---|---|---|
| proved Lean premises only | 7/3 | 245 edges (unconditional) |
| + (2,2,3) | 5/2 | 244 (existing conditional theorem) |
| + (2,2,4), (2,3,2), (3,2,3), (4,1,4..6) | 14/5 | **242** (new conditional theorem) |
| + (2,4,2,3) | 3 | **241** (new conditional theorem) |

The constants follow from `5*T >= 14*(v-2) - 12 + 40` and `T >= 3*(v-2) - 4 + 8` respectively. Exact dynamic programming over count sequences, in `scripts/aggregate.py`, confirms that the patterns admit 243 and 242 vertices. They exclude one more vertex in each case.

## What is not established

- **The geometric bridge.** A snake with such a window can be normalized so that the window has a canonical shape, by a translation and a coordinate permutation. Its intersection with the ball then satisfies every clause. That argument is short and standard, but it is not formalized here. The same gap exists for the earlier radius-three (2,2,3) certificates in `milestones/07-window-223/`.
- **DRAT is not Lean.** `drat-trim` is an independent, widely used checker, but it is not part of the Lean kernel. The CNF generator is also unverified, though the positive controls exercise it. Converting these certificates into Lean, as was attempted for (2,2,3), remains open.
- **The bound 241 is not a ceiling of the method.** Survey cases not yet run were treated as feasible. Larger radii, longer windows, and the empty-square term `s0` were not used. Solver probes at radius four suggest that a count-one vertex forces at least four empty squares near it; at radius three nothing is forced. This direction is unexplored.

## Reproduction

From the repository root, with `python-sat` installed:

```sh
cd milestones/10-window-aggregate/scripts
python survey.py --centers 3 --radius 3 --kmax 6 --out ../data/survey_c3_r3.json
python aggregate.py --survey ../data/survey_c3_r3.json
python certify.py
python controls.py
```

`wincert.ensure_drat` compiles the vendored `drat-trim` into the ignored `.build/` directory after checking its source hash. For the Lean modules, run `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib`. It now includes the three new modules and audits both conditional theorems.
