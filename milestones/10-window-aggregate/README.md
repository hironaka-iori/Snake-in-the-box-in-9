# Window exclusions and stronger aggregate bounds

Checkpoint: 18 October 2026.

**Status.** Every snake in Q9 has at most **242 edges**, and at most **241 edges**: both are now unconditional Lean theorems (`UpperBound241.lean`), so the checked interval is **191 <= a(9) <= 241**. Their premises, exclusions of 22 singleton-count windows on three or four consecutive internal path vertices, are proved in Lean by a geometric bridge to a local CNF, clause-by-clause soundness of its UNSAT core, and a kernel replay of the drat-trim LRAT refutation with a verified checker (see *Lean proofs of the 22 exclusions* below). Two further bounds remain *conditional*: at most **239 edges** from a direction-aware automaton with 145 window exclusions, and at most **238 edges** with five-centre windows (325 exclusions). Each of their premises has a **DRAT-checked** certificate for an explicit local CNF; for 239 the bridge and clause soundness are also proved in Lean, and only the kernel replay of the 145 refutations is not yet complete.

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
2. **Survey** (`scripts/survey.py`, `data/survey_*.json`). Every 3-center count triple with entries 1..6 was decided in both shapes. CaDiCaL with this encoding and an independent CP-SAT model agree on all 432 cases. Of the 216 triples, 144 are feasible in some shape. The minimum mean count over sequences whose consecutive triples are feasible is **14/5**. The worst cycle is `2,3,3,2,4`. The current Lean premises give **7/3**.
3. **Ceiling with four windows** (`data/survey_c4_r3_k5.json`). Every count quadruple in 1..5 was decided in each 4-center shape whose 3-center subwindows are feasible: 654 cases, 293 infeasible. A window `x_0..x_5` with counts `(2,4,2,3)` or `(3,2,4,2)` is infeasible in all three 4-center shapes, and adding only this exclusion raises the minimum mean to **3**. With the complete table the shape-blind minimum mean is still exactly 3, since for example `(3,3,3,3)` is feasible in shape `0,1,2,3,0`. So **241 edges is the limit of shape-blind radius-three windows of length at most four.**
4. **Certificates** (`scripts/certify.py`, `certificates/`, `data/certificates.json`). There are 22 cases:
   - 16 for the triples, in both shapes and both orientations: `(2,2,3)`, `(2,2,4)`, `(2,3,2)`, `(3,2,3)`, and `(4,1,c)` with `4<=c<=6`;
   - 6 for `(2,4,2,3)` and its reversal.

   CaDiCaL produced each DRUP proof. The repository's vendored `drat-trim` verified every one (`work/keep96/vendor/drat-trim`, source hash checked). The gzipped CNF and proof files are about 19 MB.
5. **Positive controls** (`scripts/controls.py`, `data/controls.json`). There are 532 windows: from the 131 bank snakes, the 191-edge witness, and the 137-edge count-one counterexample, including counts 1 and 3. Each satisfies every clause of its CNF with its true counts and selection.
6. **Lean.**
   - `work/spectral/stronger/WindowPotential242.lean` and `WindowPotential241.lean` use core Lean only. They prove the sequence inequalities `14*n <= 5*sum + 12` and `3*n <= sum + 4` by potentials checked by kernel evaluation of finite tables.
   - `AggregateWindowConditional.lean` uses mathlib and combines them with the existing incidence identity. It proves `upper_242_of_certified_windows` and `upper_241_of_certified_windows` for the original `Snake9.Snake`.
   - The (2,2,2) case is discharged by the existing theorem, and the count-one neighbour bound and endpoint bound are reused. Only the listed window premises remain as hypotheses.
   - *Reproduction:* a fresh source-only run of `verify_strengthened.py` succeeded. It covered 156 steps: core, incidence theorem, every strengthening module including these three, and the final audit. Both conditional theorems, and the unconditional 245 interval, audit to `propext`, `Classical.choice`, and `Quot.sound` only. The manifest and combined log are `outputs/strengthened-window-reproduction-manifest.json` and `outputs/strengthened-window-reproduction.log`. The run used `--core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget`, the only core modules the chain imports.

7. **Independent judge** (`scripts/judge.py`, `data/judge.json`). This is a high-level decision procedure that reuses none of the generating code. Its verdict is **ACCEPT**:
   - (A) It re-encodes every premise from the definitions, with a different variable order and a different cardinality encoding. It checks the recorded cycle cuts are genuine cycles, refutes each formula with Glucose, and verifies each proof with `drat-trim`. All 22 are verified.
   - (B) It classifies every vertex-only clause of the stored certificates semantically as a window unit, a degree-3 star, an interior-neighbour clause, a 4- or 6-cycle of a face, or a cycle cut. None is unclassified.
   - (C) It normalises 4,979 windows of real snakes, every window with a count at most 4 plus a sample. Each satisfies the judge's encoding with its true counts.
   - (D) An independent dynamic program reproduces 245 for the proved premises and 244 for the existing (2,2,3) condition, and gives 242 and 241 for the new premise sets.

   This gives two independent implementations of the encoding, but it is still a test of the bridge, not a proof. The bridge is now proved in Lean (next item), which supersedes this test for the 22 windows.

8. **Lean proofs of the 22 exclusions** (core Lean in `work/final_lean/` unless noted).
   - `LocalWindowModel.lean` fixes `Axioms S E window centres`: necessary conditions on the vertex set `S` and endpoint set `E` of a snake whose window sits in canonical position. `LocalWindowBridge.lean` moves every snake window there by a translation and a coordinate permutation, proves `Axioms`, and identifies the local count with the core count.
   - `scripts/gen_lean_core.py` trims each CNF/DRUP pair with drat-trim to an UNSAT core (`LocalWindowCnf/`). `scripts/gen_lean_sat.py` proves that every core clause follows from `Axioms` (`LocalWindowSat/`, theorem `sat`), so the CNF generator is not trusted.
   - `scripts/gen_lean_lrat.py` turns the drat-trim LRAT proof into proof data and kernel checks (`LocalWindowUnsat/C*`): `LratCheck.lean` is a reverse-unit-propagation checker written for kernel evaluation, with a Lean soundness proof; the proof is cut into segments of tens of thousands of hints, each checked by `decide +kernel`, with checkpoints of the live clauses. drat-trim is therefore not trusted either.
   - `LocalWindowRefuted.lean` combines them into `allRefuted : AllRefuted`, and `work/spectral/stronger/UpperBound241.lean` proves `upper_bound_242`, `upper_bound_241` and `verified_interval_191_241`. Their axioms are exactly `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).
   - *Builds.* The core closure has 1086 modules; 203 are kernel checks of 2-4.5 GB each, and must be built through `work/guarded_lake_build.py` (bounded concurrency and memory), never a plain `lake build`. Audited on macOS (2.3 kernel-hours; `outputs/upper-bound-241-audit.log`) and again from a fresh Linux environment (Lean 4.19.0, mathlib c44e0c8 built from source, 4 cores and 15 GB; 5.7 kernel-hours under CPU contention, 183 min wall time for the core and 19 min for the 152-module mathlib chain; `outputs/upper-bound-241-audit-linux.log`).

| Assumed window exclusions | Minimum mean | Bound |
|---|---|---|
| proved Lean premises only | 7/3 | 245 edges (unconditional) |
| + (2,2,3) | 5/2 | 244 (existing conditional theorem) |
| + (2,2,4), (2,3,2), (3,2,3), (4,1,4..6) | 14/5 | **242** (now unconditional) |
| + (2,4,2,3) | 3 | **241** (now unconditional) |

The constants follow from `5*T >= 14*(v-2) - 12 + 40` and `T >= 3*(v-2) - 4 + 8` respectively. Exact dynamic programming over count sequences, in `scripts/aggregate.py`, confirms that the patterns admit 243 and 242 vertices. They exclude one more vertex in each case.


## Direction-aware automaton: conditional bound 239

The shape-blind ceiling above is 3 (241 edges). Tracking which coordinates the path uses breaks it, because the only low-count windows that survive at radius three are tied to particular transition shapes, and consecutive windows of those shapes cannot be chained for long.

**Abstraction** (`scripts/refine.py`). A state is the canonical shape of the last six transition directions, up to relabelling (12 induced shapes), together with the last three lumped counts (`min(alpha,6)`, 216 combinations): 2592 states. A transition appends one direction label and one count. It is allowed unless the seven-direction block is not an induced path or some window of two, three or four consecutive centres ending at the new vertex is known to be infeasible in the radius-three local model. Unknown windows are allowed, so the automaton over-approximates real snakes and its minimum cycle mean is a valid lower bound on the average internal count given the exclusions it uses.

**Refinement.** Howard's policy iteration finds a minimum-mean cycle; the windows on it are sent to the SAT oracle; infeasible ones are added. With six directions of memory the mean rises from 8/3 to **10/3** in five rounds (four or five directions stall at 3; seven add nothing). With five-centre windows and seven directions it reaches **7/2**.

**Minimal exclusions** (`scripts/minimize.py`). Of 333 relevant infeasible windows, dual slack pruning keeps the mean 10/3 and the integer potential (range 8) with **145**; an exact-greedy pass over the vertex bound reaches 93 (mean 23/7, same bound by dynamic programming). The potential route uses the 145 set:

| route | exclusions | mean | potential range | edge bound |
|---|---|---|---|---|
| L=6, k=4 (potential, Lean) | 145 | 10/3 | 8 | **239** |
| L=6, k=4 (exact DP) | 93 | 23/7 | — | 239 |
| L=7, k=5 (potential, Lean) | 325 | 7/2 | 6 | **238** |

Arithmetic for 239: the potential gives `3 Σ_{j=6}^{m-1} min(alpha_j,6) ≥ 10 (m-6) - 8`; with `alpha_1..alpha_5 ≥ 1` and endpoints at least four, `3 T ≥ 10 m - 36`; with `T ≤ 9214 - 35 (m+1)` this is `115 m ≤ 27573`, so `m ≤ 239`.

**Certificates** (`scripts/certify_direction.py`, `data/direction_certificates.json`, `certificates/direction/*.cnf.gz`). Every one of the 145 windows has a drat-trim-verified refutation. The CNF files are committed; the DRUP proofs (250 MB) are not, their SHA256 is recorded and the script regenerates them. `scripts/judge.py --index` re-encodes all 145 independently and refutes them with Glucose: 145 verified (one case needed a solo rerun because the batch hit the checker's time limit under CPU contention; `data/judge_direction.json`). `scripts/direction_bound.py` rebuilds the automaton from the certificate index alone, checks the integer potential on every one of the 29,559 allowed edges and recomputes the exact bound (`data/direction_bound_L6_k4.json`). The 325-window set for 7/2 is certified the same way (`data/direction_certificates_k5.json`, all 325 verified; `data/direction_bound_L7_k5.json` re-checks its potential and bound; the independent judge re-encodes and refutes all 325, `data/judge_direction_k5.json`). Certifying it became practical only after the lazy cycle-cut loop was made incremental (one CaDiCaL instance per window instead of a cold restart per cut): the remaining 219 windows then took minutes instead of hours.

**Lean.** Six modules in `work/spectral/stronger/`:

- `WindowAutomatonDefs.lean` (core Lean): first-occurrence relabelling `canon`, restricted growth strings, the parity test `inducedPattern` (a block of directions must not have all multiplicities even, nor exactly one odd when it has two or more steps), enumeration helpers.
- `WindowAutomatonData.lean` (generated by `scripts/gen_lean_automaton.py`): the exclusion table and the potential as bitmask literals, the step test `check`, and `step_table : allRGS 7 0 check = true`, which the kernel evaluates in about a minute (877 restricted growth strings times 1296 count combinations). The generator re-implements `check` in Python and asserts it on the same 29,559 transitions before writing the file.
- `WindowAutomatonLemmas.lean` (core): `canon` is invariant under injective relabelling, as is `inducedPattern`; so the table applies to an arbitrary seven-direction window (`step_raw`).
- `WindowAutomatonSequence.lean` (core): the telescoped inequality `total_bound : 10 m ≤ 3 Σ_{j=1}^{m-1} alpha_j + 60`.
- `WindowAutomatonBridge.lean` (core, imports the standard-library core): `pathDir` extracts the flipped coordinate of each edge; the XOR of a block of unit vectors has bit `b` equal to the parity of the count of `b`, so `distinct` and `induced` of `Snake9.Snake` give `inducedPattern` for every window.
- `AggregateDirectionConditional.lean` (mathlib): `upper_239_of_direction_windows`. Its only premise is that no two-, three- or four-centre window of the snake has a direction shape and lumped counts listed in `forbMask`; everything else is proved.

The five-centre automaton (34 shapes, 44,064 states) is handled the same way by `WindowAutomaton5Data/Table/Sequence.lean` and `AggregateDirection238Conditional.lean` (`upper_238_of_direction_windows5`). Its step table is too large for one kernel evaluation (a single file was killed after 12 minutes), so `scripts/gen_lean_automaton5.py` emits one module per canonical 7-shape, `WindowAutomaton5Shard0..33.lean`, each enumerating the next label and all 6^5 symbol combinations in about a minute, and a kernel-checked membership lemma shows every induced restricted growth string of length eight is a listed shape followed by a label below nine (`check5_of_rgs`). Arithmetic: `2 Σ_{j=7}^{m-1} min(alpha_j,6) ≥ 7 (m-7) - 6`, so `2 T ≥ 7 m - 21 - 6` and `77 m ≤ 18385`, giving `m ≤ 238`.

All of these audit to `propext`, `Classical.choice`, `Quot.sound`. They are included in `verify_strengthened.py`; a fresh 200-step source-only run (core, incidence, every strengthening module including the 34 shards, final audit) is recorded in `outputs/strengthened-direction-reproduction-manifest.json` and `outputs/strengthened-direction-reproduction.log`.

Reproduce:

```sh
cd milestones/10-window-aggregate/scripts
python refine.py --L 6 --k 4 --K 5 --radius 3          # refinement; writes data/refine_L6_k4_K5_r3.json
python minimize.py --L 6 --k 4 --K 5 --target-edges 239
python certify_direction.py --set ../data/minimal_L6_k4_K5.pass1.json
python direction_bound.py --index ../data/direction_certificates.json --L 6 --k 4 --K 5
python judge.py --index ../data/direction_certificates.json
python gen_lean_automaton.py --index ../data/direction_certificates.json
```

The first command needs the survey files as a seed and about ten minutes; the rest take a few minutes each.

**Geometric bridge (Lean).** `AggregateDirectionUnconditional.lean` proves `upper_239_of_refuted (h : AllRefuted239) (p : Snake m) : m ≤ 239`, where `AllRefuted239` (`work/final_lean/LocalWindowDirKeys.lean`) is the conjunction of the 145 statements `Refuted (winOf ds) (boundsOf syms)`, one per certificate key. The window premises of `upper_239_of_direction_windows` are discharged in `DirectionWindowBridge.lean`: `cover_table` (kernel evaluation) shows that every set bit of `forbMask` looked up for a canonical shape of two to four centres is one of the 145 keys; first-occurrence relabelling is realised by a coordinate permutation; and the reversed lookup of `wforb` is the same statement for the reversed snake (`LocalWindowDirBridge.lean`, core, reuses the frame of `LocalWindowBridge`). On the certificate side, `scripts/gen_lean_core.py --set direction` trims each committed CNF/DRUP pair with drat-trim to an UNSAT core (`LocalWindowCnf/D<dirs>A<syms>.lean`, 244,777 clauses in total; hashes and LRAT statistics in `data/lean_core_direction/`), and `scripts/gen_lean_sat.py --set direction` proves that every core clause follows from the snake axioms (`LocalWindowSat/D*.lean`, theorem `sat`). `LocalWindowDirSat.allRefuted239_of_unsat` turns the 145 core refutations into `AllRefuted239`. For the 48 windows with cycle cuts the committed CNF/DRUP pairs match the SHA256 values of `direction_certificates_k5.json`, not the stale ones of `direction_certificates.json`.

**Kernel replay of the 145 refutations.** `scripts/run_direction_replays.py gen` writes the replays `LocalWindowUnsat/D*` (not committed; 145 roots, 12,879 data and check modules, 1.9 GB of source, six cases with 14-bit words) and `run_direction_replays.py build` builds their 2575 kernel-check modules through the guarded builder. The drat-trim LRAT proofs total about 4.1 million lemmas and 249 million hints, 40% of them in four windows. The checker is `work/final_lean/LratFast.lean` (variants `LratFast14`, `LratFastO3k*`, `LratFastO4k*` for wider words and literal offsets, generated by `scripts/gen_checker_variants.py`): the same proof format and soundness argument as `LratCheck.lean`, but every kernel-evaluated operation is a kernel-accelerated `Nat` primitive, the initial database is a perfect tree built by one recursion, and a checkpoint is a stream of clause words packed 64 nodes per `Nat` (`build`/`pre`, validated by `cpOk`, so soundness does not depend on the parser). Measured against `LratCheck`: one 25,000-hint segment 74 s -> 21 s, the initial database 16 s -> 2.4 s. Generated proof data are `noncomputable def` (no compiled code; build output several times smaller), data modules import their predecessor only when their start is a replay of it, and check modules import their segments' data modules explicitly, so no module maps more than a few dozen oleans. `LocalWindowDirUnsat.lean` (generated by `gen_lean_sat.py --set direction`) combines the replays with `LocalWindowSat/D*` into `allRefuted239`, and `work/spectral/stronger/UpperBound239.lean` gives `upper_bound_239`. **Status:** the replay build is running (Linux, 4 cores / 15 GB; the two largest windows need about 1000 segments each), so 239 is still conditional.

**Towards 238 (five-centre windows).** The 325 keys of `direction_certificates_k5.json` contain the 145 keys of the 239 set. `scripts/gen_lean_core.py --set direction5` reuses those cores and, for the 180 new windows, extracts the UNSAT core with the toolchain's CaDiCaL (`--lrat`, trimmed to the dependencies of the empty clause; 30-40% smaller than drat-trim's proofs). Only the core is committed (`LocalWindowCnf/D*.lean`, `data/lean_core_direction5/`); the LRAT replayed in Lean is produced from the core alone (`core_lrat`, ids remapped to the committed CNF) on whichever machine builds the replays, so any UNSAT proof of the core does, and the kernel re-checks every hint. The 36 five-centre CNFs have up to 2899 variables, beyond the offset 2400 of the first checkers: `LratFastO3k*` use offset 3000. The Lean chain is generated: `LocalWindowDirKeys5.lean` (325 keys, `AllRefuted238`), `gen_lean_sat.py --set direction5` (clause soundness `LocalWindowSat/D*`, `LocalWindowDirSat5`, `LocalWindowDirUnsat5`), and `scripts/gen_lean_chain5.py` (`DirectionWindowBridge5`, `AggregateDirection238Unconditional`, `UpperBound238`). `gen_lean_automaton5.py` now emits one exclusion mask per window shape and one potential table per 7-shape (`forbMaskOf5`, `potMaskOf5`): a kernel lookup of the former 143k/176k-bit tables shifted the whole table and every shifted copy stayed in the kernel's term cache, which made the shards and the cover theorem exceed 12 GB; with per-shape masks a shard takes 60-95 s and 3.2 GB and the whole chain to `upper_238_of_refuted` compiles in 39 minutes (Linux, standard axioms). **Status:** cores, clause-soundness modules and replays of the 180 new windows are being generated; 238 is still conditional.

**Radius 4 (towards 236).** The local model `Axioms` of `LocalWindowModel.lean` does not depend on the ball radius (the radius only decides which variables the CNF has), so radius-4 certificates go through the same bridge. `refine.py --radius 4` (oracle cache entries are keyed by radius): with L=7, k=5, K=5 the minimum mean rises from 7/2 to 42/11 (`data/refine_L7_k5_K5_r4.json`, potential range 44), which the Lean arithmetic turns into **236** (42 m <= 11 sum + 291 with a 6-bit potential, then 427 m <= 101172); with L=6, k=5, K=8 it reaches 4 (`refine_L6_k5_K8_r4.json`), also 236 by the potential route (39 m <= 9205) but needing the cap K generalised in Lean. `minimize.py --radius 4`, `certify_direction.py --radius 4 --certs-dir ../certificates/direction_r4`, `gen_lean_core.py --set r4`, `gen_lean_automaton5.py --tag R4 --pot-bits 6` and `gen_lean_chain5.py --tag R4 --bound 236` are prepared for the certified set; `LratFastO4k*` cover CNFs with up to 3999 variables.

**Still not established beyond that.** The 208-vertex adversary of `milestones/11-local-ceiling/` satisfies every radius-3 window of up to five centres and every radius-4 window of up to four centres, so these families are capped near 227 edges; its five-centre radius-4 windows have not been tested. The levers after 236 are more memory (L=7) and a higher cap at radius 4, radius 5, six-centre windows, and the empty-square term.

## What is not established

- **The 238 premises.** The 325 five-centre windows have DRAT-checked certificates only; their bridge, clause soundness and replays are not done. For 239 see the replay status above. (The bridge and the DRAT-to-Lean gap described in earlier checkpoints are closed for the 22 windows behind 242 and 241.)
- **Beyond 241.** The shape-blind four-window ceiling is 3, so further progress here needs more information:
  - *Direction-aware states.* Feasible low quadruples such as `(3,3,3,3)` occur only in shape `0,1,2,3,0`. Three consecutive windows of that shape would make `x_7` adjacent to `x_0`, so an automaton that also tracks directions should exceed mean 3. `scripts/direction_automaton.py` does this: it tracks the last seven directions and checks each window against the survey for its own shape. Its minimum mean is about **10/3**, found by binary search. With small constants that would give roughly 239–240 edges. It relies on many more solver-only exclusions, none certified yet.
  - *Radius four.*
  - *The empty-square term `s0`, which every current bound discards.* A CP-SAT probe at radius four found that a count-one vertex forces at least four empty squares meeting its neighbours. At radius three nothing is forced. This is uncertified.

## Reproduction

From the repository root, with `python-sat` installed:

```sh
cd milestones/10-window-aggregate/scripts
python survey.py --centers 3 --radius 3 --kmax 6 --out ../data/survey_c3_r3.json
python survey.py --centers 4 --radius 3 --quads quads.json --out ../data/survey_c4_r3_k5.json   # quads.json: the alpha lists in survey_c4_r3_k5.json
python aggregate.py --survey ../data/survey_c3_r3.json
python certify.py
python controls.py
python judge.py                 # independent end-to-end verdict
python direction_automaton.py   # exploratory, about 10/3
```

`wincert.ensure_drat` compiles the vendored `drat-trim` into the ignored `.build/` directory after checking its source hash. For the Lean modules, run `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib --core-targets LocalWindowRefuted LocalWindowBridge Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget`; it builds the core through `work/guarded_lake_build.py` and audits the conditional and the unconditional theorems. `--with-239` adds `UpperBound239` once the 145 replays have been generated.
