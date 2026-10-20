# Window exclusions and stronger aggregate bounds

Checkpoint: 19 October 2026.

**Status.**

- Every snake in Q9 has at most **237 edges**. This is an unconditional Lean theorem (`work/spectral/stronger/UpperBound237.lean`: `upper_bound_237`, `verified_interval_191_237`), so the checked interval is now **191 <= a(9) <= 237**. Its axioms are only `propext`, `Classical.choice`, `Quot.sound` (`outputs/upper-bound-237-audit-linux.log`: `chain_audit.py --target UpperBound237`, Linux, Lean 4.19.0, mathlib c44e0c8e; `UpperBound237` itself took 97 s and 10.9 GB, the chain modules were reused from the compile of `outputs/aggregate-237-conditional-chain-linux.log`).
  - It rests on the five-centre automaton with **radius-four** windows (mean 51/14, 6-bit potential of range 61) and **387** window exclusions, kept by `scripts/prune_costly.py --target-edges 237` from the 1351-window minimal radius-four set; all are DRAT-certified (`data/direction_certificates_r4b.json`).
  - Each of the 387 exclusions is a Lean theorem: geometric bridge `DirectionWindowBridge5R4b`, packed clause soundness `LocalWindowSat/Q*` (collected in `LocalWindowDirSatR4b`), and kernel replay of a CaDiCaL-portfolio LRAT refutation of its UNSAT core (289 M hints in total) through `LratFast2`, with `LratFast2F` (`check2f`) on segments of more than 2000 lemmas, compiled with `lean` directly (`--direct`). The replays built completely: 17,197/17,197 modules, 0 failed; 3,287 check modules, 34.0 kernel-hours, about 12 h (three runs, two container restarts) wall time; `LocalWindowDirUnsatR4b` in 77 s at 7.75 GB peak (`outputs/upper-bound-237-replay-linux.log`).
  - *Scope of the check.* As for 238, the audit was made on Linux only, against the incrementally built core (not a fresh source-only rebuild); `verify_strengthened.py` has no `--with-237` switch yet.
- The earlier step, at most **238 edges**, remains an unconditional Lean theorem (`work/spectral/stronger/UpperBound238.lean`: `upper_bound_238`, `verified_interval_191_238`). Its axioms are only `propext`, `Classical.choice`, `Quot.sound` (`outputs/upper-bound-238-audit-linux.log`: `chain_audit.py --target UpperBound238`, Linux, Lean 4.19.0, mathlib c44e0c8e; `UpperBound238` itself took 163 s and 9.7 GB, the chain modules were reused from the compile of `outputs/aggregate-238-chain-175-linux.log`).
  - It rests on the five-centre automaton (mean 7/2, potential range 10) with **175** window exclusions, pruned by `scripts/prune_costly.py` from the 325 certified five-centre windows; the 175 include 119 of the 239 set.
  - Each of the 175 exclusions is a Lean theorem: geometric bridge `DirectionWindowBridge5`, clause soundness `LocalWindowSat/D*` (collected in `LocalWindowDirSat5`), and kernel replay of the LRAT refutation of its UNSAT core. The replays built completely: 14,206/14,206 modules, 0 failed; 2,803 check modules, 39.5 kernel-hours over all runs, at most 3.93 GB each; 11,038 data modules (13.5 h); `LocalWindowDirUnsat5` in 230 s at 7.63 GB peak (`outputs/upper-bound-238-replay-linux.log`).
  - *Scope of the check.* The audit was made on Linux only, against the incrementally built core (not a fresh source-only rebuild). The fresh reproduction path `python work/spectral/verify_strengthened.py --with-238` has not been run yet.
- The earlier step, at most **242 edges** and at most **241 edges** (`UpperBound241.lean`), remains unconditional and audited on macOS and from a fresh Linux environment. Its premises, exclusions of 22 singleton-count windows on three or four consecutive internal path vertices, are proved in Lean by a geometric bridge to a local CNF, clause-by-clause soundness of its UNSAT core, and a kernel replay of the drat-trim LRAT refutation with a verified checker (see *Lean proofs of the 22 exclusions* below).
- At most **239 edges**, from the direction-aware automaton with 145 window exclusions, stays a **conditional** theorem. It is subsumed by 238, so the replay of its 145 refutations was stopped unfinished.
- Every exclusion of both sets has a DRAT-checked certificate of an explicit local CNF.
- Radius-4 windows reach mean 42/11, which gives **236** with the 732-window set (371 shared with the 237 set; all DRAT-certified, `data/direction_certificates_r4c.json`). Its conditional chain compiles with standard axioms (`outputs/aggregate-236-conditional-chain-linux.log`), its cores and clause-soundness modules are built, and the replays of the 361 new windows are being generated and built; 236 is not a theorem yet.
- Local window methods of this kind are capped near 227 edges (`milestones/11-local-ceiling/`).

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


## Direction-aware automaton: conditional bound 239, unconditional bound 238

The shape-blind ceiling above is 3 (241 edges). Tracking which coordinates the path uses breaks it, because the only low-count windows that survive at radius three are tied to particular transition shapes, and consecutive windows of those shapes cannot be chained for long.

**Abstraction** (`scripts/refine.py`). A state is the canonical shape of the last six transition directions, up to relabelling (12 induced shapes), together with the last three lumped counts (`min(alpha,6)`, 216 combinations): 2592 states. A transition appends one direction label and one count. It is allowed unless the seven-direction block is not an induced path or some window of two, three or four consecutive centres ending at the new vertex is known to be infeasible in the radius-three local model. Unknown windows are allowed, so the automaton over-approximates real snakes and its minimum cycle mean is a valid lower bound on the average internal count given the exclusions it uses.

**Refinement.** Howard's policy iteration finds a minimum-mean cycle; the windows on it are sent to the SAT oracle; infeasible ones are added. With six directions of memory the mean rises from 8/3 to **10/3** in five rounds (four or five directions stall at 3; seven add nothing). With five-centre windows and seven directions it reaches **7/2**.

**Minimal exclusions** (`scripts/minimize.py`). Of 333 relevant infeasible windows, dual slack pruning keeps the mean 10/3 and the integer potential (range 8) with **145**; an exact-greedy pass over the vertex bound reaches 93 (mean 23/7, same bound by dynamic programming). The potential route uses the 145 set:

| route | exclusions | mean | potential range | edge bound |
|---|---|---|---|---|
| L=6, k=4 (potential, Lean) | 145 | 10/3 | 8 | **239** |
| L=6, k=4 (exact DP) | 93 | 23/7 | — | 239 |
| L=7, k=5 (potential, Lean) | 175 (pruned from 325) | 7/2 | 10 | **238** |

Arithmetic for 239: the potential gives `3 Σ_{j=6}^{m-1} min(alpha_j,6) ≥ 10 (m-6) - 8`; with `alpha_1..alpha_5 ≥ 1` and endpoints at least four, `3 T ≥ 10 m - 36`; with `T ≤ 9214 - 35 (m+1)` this is `115 m ≤ 27573`, so `m ≤ 239`.

**Certificates** (`scripts/certify_direction.py`, `data/direction_certificates.json`, `certificates/direction/*.cnf.gz`). Every one of the 145 windows has a drat-trim-verified refutation. The CNF files are committed; the DRUP proofs (250 MB) are not, their SHA256 is recorded and the script regenerates them. `scripts/judge.py --index` re-encodes all 145 independently and refutes them with Glucose: 145 verified (one case needed a solo rerun because the batch hit the checker's time limit under CPU contention; `data/judge_direction.json`). `scripts/direction_bound.py` rebuilds the automaton from the certificate index alone, checks the integer potential on every one of the 29,559 allowed edges and recomputes the exact bound (`data/direction_bound_L6_k4.json`). The 325-window set for 7/2 is certified the same way (`data/direction_certificates_k5.json`, all 325 verified; `data/direction_bound_L7_k5.json` re-checks its potential and bound; the independent judge re-encodes and refutes all 325, `data/judge_direction_k5.json`). Certifying it became practical only after the lazy cycle-cut loop was made incremental (one CaDiCaL instance per window instead of a cold restart per cut): the remaining 219 windows then took minutes instead of hours.

**Lean.** Six modules in `work/spectral/stronger/`:

- `WindowAutomatonDefs.lean` (core Lean): first-occurrence relabelling `canon`, restricted growth strings, the parity test `inducedPattern` (a block of directions must not have all multiplicities even, nor exactly one odd when it has two or more steps), enumeration helpers.
- `WindowAutomatonData.lean` (generated by `scripts/gen_lean_automaton.py`): the exclusion table and the potential as bitmask literals, the step test `check`, and `step_table : allRGS 7 0 check = true`, which the kernel evaluates in about a minute (877 restricted growth strings times 1296 count combinations). The generator re-implements `check` in Python and asserts it on the same 29,559 transitions before writing the file.
- `WindowAutomatonLemmas.lean` (core): `canon` is invariant under injective relabelling, as is `inducedPattern`; so the table applies to an arbitrary seven-direction window (`step_raw`).
- `WindowAutomatonSequence.lean` (core): the telescoped inequality `total_bound : 10 m ≤ 3 Σ_{j=1}^{m-1} alpha_j + 60`.
- `WindowAutomatonBridge.lean` (core, imports the standard-library core): `pathDir` extracts the flipped coordinate of each edge; the XOR of a block of unit vectors has bit `b` equal to the parity of the count of `b`, so `distinct` and `induced` of `Snake9.Snake` give `inducedPattern` for every window.
- `AggregateDirectionConditional.lean` (mathlib): `upper_239_of_direction_windows`. Its only premise is that no two-, three- or four-centre window of the snake has a direction shape and lumped counts listed in `forbMask`; everything else is proved.

The five-centre automaton (34 shapes, 44,064 states) is handled the same way by `WindowAutomaton5Data/Table/Sequence.lean` and `AggregateDirection238Conditional.lean` (`upper_238_of_direction_windows5`). Its step table is too large for one kernel evaluation (a single file was killed after 12 minutes), so `scripts/gen_lean_automaton5.py` emits one module per canonical 7-shape, `WindowAutomaton5Shard0..33.lean`, each enumerating the next label and all 6^5 symbol combinations in about a minute, and a kernel-checked membership lemma shows every induced restricted growth string of length eight is a listed shape followed by a label below nine (`check5_of_rgs`). Arithmetic: `total_bound5`: `7 m ≤ 2 Σ_{j=1}^{m-1} α_j + 52` (`WindowAutomaton5Sequence.lean:131`). This is the general form `(P + 35Q) m ≤ 9171 Q + C` with `C = (2^bits − 1) + 7P − 6Q` (`scripts/prune_costly.py`); for P/Q = 7/2 and a 4-bit potential it is `77 m ≤ 18394`, so `m ≤ 238`.

All of these audit to `propext`, `Classical.choice`, `Quot.sound`. They are included in `verify_strengthened.py`; a fresh 200-step source-only run (core, incidence, every strengthening module including the 34 shards, final audit; 17 October, with the earlier 325-window tables) is recorded in `outputs/strengthened-direction-reproduction-manifest.json` and `outputs/strengthened-direction-reproduction.log`.

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

**Kernel replay of the 145 refutations.** `scripts/run_direction_replays.py gen` writes the replays `LocalWindowUnsat/D*` (not committed; 145 roots, 12,879 data and check modules, 1.9 GB of source, six cases with 14-bit words) and `run_direction_replays.py build` builds their 2575 kernel-check modules through the guarded builder. The drat-trim LRAT proofs total about 4.1 million lemmas and 249 million hints, 40% of them in four windows. The checker is `work/final_lean/LratFast.lean` and its generated variants; the checker, data format and build are described under *How the replays work and how to reproduce them* below. Measured against `LratCheck`: one 25,000-hint segment 74 s -> 21 s, the initial database 16 s -> 2.4 s. `LocalWindowDirUnsat.lean` (generated by `gen_lean_sat.py --set direction`) combines the replays with `LocalWindowSat/D*` into `allRefuted239`, and `work/spectral/stronger/UpperBound239.lean` gives `upper_bound_239`. **Status:** stopped unfinished; no `UpperBound239` build or audit exists. The 238 set covers 119 of these windows and an unconditional 238 subsumes 239. The same pruning would keep 96 of the 145 windows (156 M of 249 M hints; `data/certified_L6_k4_K5_pruned*.json`) if 239 is ever needed on its own.

**The bound 238 (five-centre windows).** The 175 keys of `direction_certificates_k5p.json` (a subset of the 325 of `direction_certificates_k5.json`, selected by `scripts/prune_costly.py` with the mean still 7/2 and potential range 10; LRAT hints 869 M -> 270 M) contain 119 of the 145 keys of the 239 set. `scripts/gen_lean_core.py --set direction5` reuses those cores and, for the new windows (180 of the 325, of which 56 remain in the 175), extracts the UNSAT core with the toolchain's CaDiCaL (`--lrat`, trimmed to the dependencies of the empty clause; 30-40% smaller than drat-trim's proofs). Only the core is committed (`LocalWindowCnf/D*.lean`, `data/lean_core_direction5/`); the LRAT replayed in Lean is produced from the core alone (`core_lrat`, ids remapped to the committed CNF) on whichever machine builds the replays, so any UNSAT proof of the core does, and the kernel re-checks every hint. The 36 five-centre CNFs (18 of them in the 175 set) have up to 2899 variables, beyond the offset 2400 of the first checkers: `LratFastO3k*` use offset 3000. The Lean chain is generated: `LocalWindowDirKeys5.lean` (175 keys, `AllRefuted238`), `gen_lean_sat.py --set direction5` (clause soundness `LocalWindowSat/D*`, `LocalWindowDirSat5`, `LocalWindowDirUnsat5`), and `scripts/gen_lean_chain5.py` (`DirectionWindowBridge5`, `AggregateDirection238Unconditional`, `UpperBound238`). `gen_lean_automaton5.py` now emits one exclusion mask per window shape and one potential table per 7-shape (`forbMaskOf5`, `potMaskOf5`): a kernel lookup of the former 143k/176k-bit tables shifted the whole table and every shifted copy stayed in the kernel's term cache, which made the shards and the cover theorem exceed 12 GB; with per-shape masks a shard takes 60-95 s and 3.2 GB and the whole chain to `upper_238_of_refuted` compiled in 39 minutes (Linux, standard axioms) in its 325-key form. **Status:** done. Cores and clause-soundness modules of all 175 windows are generated and built (`LocalWindowDirSat5`, 175 Sat modules). The chain compiles in its 175-key form (potential range 10; 47 min, 34 shards at 3.4 GB; `outputs/aggregate-238-chain-175-linux.log`). The 175 replays and `LocalWindowDirUnsat5` are built (`outputs/upper-bound-238-replay-linux.log`), and `UpperBound238` audits to the standard axioms (`outputs/upper-bound-238-audit-linux.log`), so **238 is unconditional**.

**Radius 4: the bound 237, and 236 in progress.** The local model `Axioms` of `LocalWindowModel.lean` does not depend on the ball radius (the radius only decides which variables the CNF has), so radius-4 certificates go through the same bridge. `refine.py --radius 4` (oracle cache entries are keyed by radius): with L=7, k=5, K=5 the minimum mean rises from 7/2 to 42/11 (`data/refine_L7_k5_K5_r4.json`, potential range 44), which the Lean arithmetic turns into **236** (42 m <= 11 sum + 291 with a 6-bit potential, then 427 m <= 101172); with L=6, k=5, K=8 it reaches 4 (`refine_L6_k5_K8_r4.json`), also 236 by the potential route (39 m <= 9205) but needing the cap K generalised in Lean. `LratFastO4k*` and `LratFast2_O4k*` cover CNFs with up to 3999 variables. Two certified sets exist; the generator set names are `r4` (bound 236, module prefix `R`, reuses the `r4b` cores) and `r4b` (bound 237, module prefix `Q`, keys `LocalWindowDirKeysR4b`, premise `AllRefuted237`). **Status:**
- *237:* `prune_costly.py --target-edges 237` keeps 387 windows of the 1351-window minimal set (mean 51/14, potential range 61, 6-bit potential), all DRAT-certified (`data/direction_certificates_r4b.json`). Cores come from `gen_lean_core.py --set r4b` (CaDiCaL portfolio for all 387; 660,795 core clauses, 6.45 M lemmas, 289 M LRAT hints in total) and the clause-soundness modules use packed data (`LocalWindowDirSatR4b` built). The Lean chain is generated (`gen_lean_automaton5.py --tag R4b`, `gen_lean_chain5.py --tag R4b --bound 237 --P 51 --Q 14 --pot-bits 6 --shapes 13`; `51 m <= 14 sum + 336`, then `541 m <= 128730`), and the conditional theorem `upper_237_of_direction_windows5R4b` compiles with the standard axioms (`outputs/aggregate-237-conditional-chain-linux.log`). The replays were generated with `--split` (`LratFast2`, cached start database; `LratFast2F`/`check2f` on segments of more than 2000 lemmas) and built with `--direct`: 3,287 check modules, 34.0 kernel-hours, about 12 h wall time, 0 failed (`outputs/upper-bound-237-replay-linux.log`). **`UpperBound237` audited** (`outputs/upper-bound-237-audit-linux.log`, standard axioms only), so **237 is unconditional**.
- *236:* 741 windows were DRAT-certified first (`data/direction_certificates_r4.json`); the set was then re-pruned to reuse the 237 windows: 732 windows, 371 shared with the 237 set, all DRAT-certified (`data/direction_certificates_r4c.json`; `direction_bound` gives mean 42/11, potential range 48, 236 edges). The chain (`--tag R4`, 14 window shapes, `--bound 236 --P 42 --Q 11 --pot-bits 6`) compiles with standard axioms (`upper_236_of_direction_windows5R4`, `outputs/aggregate-236-conditional-chain-linux.log`); the cores (361 new, prefix `R`; 371 reuse the `Q*` modules of 237) and the packed clause-soundness modules (`LocalWindowDirSatR4`, keys `LocalWindowDirKeysR4`, premise `AllRefuted236`) are built. The replays of the 361 new windows (640 M full-CNF hints; the replay generator makes the shorter core proofs) are being generated and built; **236 is not yet unconditional**. The set keeps a few very large windows whatever the cost table, and their replay cost is extrapolated and uncertain (see *Shorter proofs and lighter data* below).

**Still not established beyond that.** The 208-vertex adversary of `milestones/11-local-ceiling/` satisfies every radius-3 window of up to five centres and every radius-4 window of up to four centres, so these families are capped near 227 edges; its five-centre radius-4 windows have not been tested. The levers after 236 are more memory (L=7) and a higher cap at radius 4, radius 5, six-centre windows, and the empty-square term.

## How the replays work and how to reproduce them

**Chain of trust for one window.**
- `LocalWindowCnf/D<dirs>A<syms>.lean` holds the UNSAT core.
- `LocalWindowSat/D*.lean` (theorem `sat`) proves that every core clause follows from the snake axioms, so the CNF generator is not trusted.
- `LocalWindowUnsat/D*.lean` (theorem `unsat`) replays an LRAT refutation of the core in the kernel, so neither drat-trim nor CaDiCaL is trusted.
- `LocalWindowDirSat5.allRefuted238_of_unsat` and `LocalWindowDirUnsat5` combine the 175 windows into `allRefuted238`, which `UpperBound238.lean` passes to `upper_238_of_refuted`.
- Of the 175 windows, 119 are shared with the 239 set and replay drat-trim's LRAT. The other 56 replay a CaDiCaL `--lrat` proof of the core, regenerated from the committed core by `gen_lean_core.core_lrat` (`data/lean_core_direction5/_summary.json`: `"cadical": 56`). The kernel checks every hint, so any UNSAT proof of the core is acceptable.
- Size: 316,876 core clauses, 4.63 M lemmas and 269.9 M hints (summary `totals`), down from 869 M for the 325-window set.

**Checker (`work/final_lean/LratFast.lean`).** It uses the same proof format and soundness proof as `LratCheck.lean`, with three changes:
- every operation the kernel evaluates is a kernel-accelerated `Nat` primitive;
- the initial database is the perfect tree `perf h 0`, built by one recursion;
- a checkpoint is a pre-order list of tree entries, built by `pre`/`build`; `cpOk` checks it against the replayed database, so soundness does not depend on the parser.

`scripts/gen_checker_variants.py` produces the variants by constant substitution: `LratFast14` and `LratFast15` widen the words to 14 or 15 bits (clause keys up to 16383 or 32767), and `LratFastO3k*` and `LratFastO4k*` move the literal offset to 3000 or 4000 for CNFs with at least 2400 or 3000 variables. `run_direction_replays.py gen` picks the offset from the variable count, then tries 13-, 14- and 15-bit words in turn. In the 238 set most windows fit 13-bit words; one window, `D01203A4433` (18.6 M hints), needs 15 bits. Offset 2400 serves 157 windows and offset 3000 the other 18.

**Faster checker for the next sets (`work/final_lean/LratFast2.lean`, `--split`; not used for the 238 build, used for the radius-4 sets).** Sampling the kernel's stacks (gdb) during a check showed the time going to tree walks for hint clauses: every hint walked the current database again (about 200 µs per lookup at depth 11), while GMP work on the clause masks was negligible (60-, 300- and 4800-bit masks time the same). About 94% of the hints of a segment name clauses that were already in the database when the segment started, on few distinct keys (about 1300 per 25,000 hints). `check2 S D ps` keeps the start database `S` fixed and inserts the segment's lemmas into a second tree `D`; a hint with the flag bit `2^(W-1)` set is looked up in `S` through `Nat.add 0 (lookC S (Nat.succ m))` with a literal `m`, a term the kernel evaluates once per key and then finds in its whnf cache. Soundness ignores the flags: every clause of `S` and of `D` is true. Checkpoints are verified by `cpZ`, which walks the checkpoint and the replayed database together (same perfect shape) instead of looking every clause up. `scripts/gen_checker_variants.py` writes `LratFast2_{14,15,16}`, `LratFast2_O3k*`, `LratFast2_O4k*` (and 16-bit `LratFast*16`, since keys must stay below `2^(W-1)`). Measured on `D01203A3352` (400,923 hints): check modules 176.5 s -> 76.0 s, peak 1.53 -> 1.05 GB. Separately, `work/guarded_lake_build.py --direct` compiles each module with `lean -o` instead of `lake build`: starting lake in this 14,000-module project costs about 5 s per call, which was most of the 13.5 h spent on the 11,038 data modules of the 238 build (data modules of `D01203A3352`: 45.3 s -> 17.8 s). Together about 2.2x less build time; `run_direction_replays.py gen --split` and `build --direct` select them. Segment size and checkpoint spacing barely matter (25k/3/4, 50k/2/2, 50k/1/2, 100k/1/1 within 10%).

**Shorter proofs and lighter data (radius-4 sets).**
- *Proof shortening* (`scripts/gen_lean_core.py`, `PORTFOLIO`, `ROUNDS`, `--rounds`): CaDiCaL is run with a portfolio of configurations and the shortest trimmed LRAT is kept; each further round re-solves the core of the previous proof. On `D01203A3352`: 400,923 -> 309,004 hints (portfolio) -> 199,958 (3 rounds); four more windows 94k -> 54k, 45k -> 36k, 1.03 M -> 753k, 2.30 M -> 1.87 M. With `LratFast2` its check modules went from 135.8 s (`LratFast`, original proof) to 45.9 s. For very large windows extra rounds cost more solver time than they save in replay time, so the largest windows of the 237 set used one round.
- *Packed clause-soundness data* (`work/final_lean/LocalWindowTagsPacked.lean`): the data were about two thirds of a Sat module's build time (31 of 47 s on `D01203A3352`: 25 s for the meaning tree, 7 s for the tags). The meaning tree (`mtB`) and the tags (`tagsOf`, `tagsOfL` in chunks of 64) are now decoded from `Nat` literals; `Tags.sound` holds for any tree and tags, so the decoders need no proof. Sat module 47.3 s -> 18.9 s, `.olean` 6.4 MB -> 117 KB. A single long tag stream was quadratic to decode (two modules exceeded 5 GB), hence the chunks. The `Cnf`/`Sat` data of the radius-4 sets are `noncomputable`: `Cnf` `.olean` 9.5 MB -> 0.8 MB, 15.4 s -> 7.8 s.
- *Cost model for pruning:* hints per DRUP line ranged from 0.1 to 17 over the 387 cored windows; the fit hints ~ 1.5e-6 * lines^2.27 (`data/est_hints_r4.jsonl`) estimates the LRAT cost of uncored windows, and `prune_costly.py --costs` prunes against such a table.

**Data format** (`scripts/gen_lean_lrat.py --fast`):
- One `Nat` per lemma, made of W-bit words, lowest first: `slot (lit+1)… 0 hint… 0`. A literal `v` / `-v` is bit `v` / `v+OFF`.
- A checkpoint holds one entry per tree node in pre-order (`0` for a free slot). An earlier packed stream made checks about twice as slow.
- All data are raw `nat_lit` literals declared `noncomputable def`: no compiled code and smaller oleans. Lists longer than 16,384 entries are written as `List.append` of 2048-entry chunks, because a 32,767-entry checkpoint overflowed the elaborator stack.
- The proof is cut into segments of about `--seg 25000` hints, each checked by one `decide +kernel`, with a checkpoint every `--cp 3` segments and `--group 4` segments per `Check<g>` module. A data module imports its predecessor only when its start is a replay of it, which keeps import chains short.

**Guarded build (`work/guarded_lake_build.py`).** It builds the import closure one module per `lake build`:
- at most `--heavy-jobs` kernel checks (modules matching `\.Check\d+$`) run at once, plus `--jobs` light modules;
- a module starts only when `--min-free-gb` of memory is available; a process group above `--rss-cap-gb` is killed, and new launches stop below `--floor-gb`;
- `--trust-mtime` marks a module done without calling lake when its `.olean` is newer than its source and than its imports' oleans, so resuming a build of over ten thousand modules takes seconds; lake re-checks its own traces when the final target is built.

Never use a plain `lake build` on these modules: it would start one kernel check per core. On Linux (4 cores, 15 GB) a replay check module took 75 s and 2.2 GB peak RSS at the median, at most about 3 minutes and 3.93 GB. The 175 replays have 2,803 check modules (39.5 kernel-hours over all runs) and 11,038 data modules (13.5 h); the final resumable run built the remaining modules of the 14,206-module closure with no failure in 12.8 h wall time on 4 shared cores with 3 concurrent kernel checks (`outputs/upper-bound-238-replay-linux.log`).

**Reproduce** (Lean 4.19.0, mathlib `c44e0c8`):

```sh
cd milestones/10-window-aggregate/scripts
# LRAT + Lean replay sources for the 175 windows (resumable; existing modules are skipped).
# The 119 windows shared with 239 read drat-trim's NAME.lrat/NAME.cnf from --work
# (gen_lean_core.py --set direction writes them); the 56 others are regenerated by core_lrat.
python run_direction_replays.py --set direction5 gen --work /path/to/lrat-direction5
cd ../../..
# clause soundness of the 175 cores
python3 work/guarded_lake_build.py LocalWindowDirSat5 --jobs 1 --heavy-jobs 1 \
    --min-free-gb 6 --rss-cap-gb 5 --trust-mtime
# kernel replays
python3 milestones/10-window-aggregate/scripts/run_direction_replays.py --set direction5 build \
    --jobs 2 --heavy-jobs 3 --min-free-gb 6 --rss-cap-gb 6 --trust-mtime
# combine, then compile and audit the mathlib chain against the built core
python3 work/guarded_lake_build.py LocalWindowDirUnsat5 --trust-mtime
python3 work/spectral/chain_audit.py --mathlib-dir /path/to/mathlib --target UpperBound238 \
    --log outputs/upper-bound-238-audit-linux.log \
    --axioms Snake9.upper_bound_238 Snake9.verified_interval_191_238
```

The generated sources and the LRAT working directory take several GB each, and the build output is larger than the sources, so check free disk space first. These steps were run on Linux (4 cores, 15 GB): the replays in `outputs/upper-bound-238-replay-linux.log`, the audit in `outputs/upper-bound-238-audit-linux.log` (AXIOM AUDIT PASSED). The fresh, source-only reproduction path is `python work/spectral/verify_strengthened.py --with-238` (with the usual `--mathlib-dir` and `--core-targets`): it copies the generated `LocalWindowUnsat/D*` modules into a new directory, builds `LocalWindowDirUnsat5` and the chain, requires the 238 axiom audits, and prints the bound actually proved. It has not been run yet.

## What is not established

- **An independent rebuild of 238 and 237.** The 175 and 387 premises are now Lean theorems and 238 and 237 are unconditional, but each was audited on one platform (Linux) against an incrementally built core. A fresh source-only run (`verify_strengthened.py --with-238`; there is no `--with-237` switch yet) and a second platform are still to do. The 239 replays were not completed (see above); 239 is subsumed. (The bridge and the DRAT-to-Lean gap described in earlier checkpoints are closed for the 22 windows behind 242 and 241 and for the 175 behind 238.)
- **Beyond 237.** The 732-window radius-4 set behind 236 is DRAT-certified and its chain compiles conditionally; its cores and clause-soundness modules are built and the replays of the 361 windows not shared with the 237 set are in progress. 236 is not a theorem yet. The notes below record how this milestone first went beyond 241.
- **Beyond 241 (historical).** The shape-blind four-window ceiling is 3, so further progress here needs more information:
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

`wincert.ensure_drat` compiles the vendored `drat-trim` into the ignored `.build/` directory after checking its source hash. For the Lean modules, run `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib --core-targets LocalWindowRefuted LocalWindowBridge Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget`; it builds the core through `work/guarded_lake_build.py` and audits the conditional and the unconditional theorems. `--with-238` adds `UpperBound238` once the 175 replays are generated (not yet run as a fresh reproduction) (`--with-239` remains for the 145-window set); see *How the replays work and how to reproduce them*.
