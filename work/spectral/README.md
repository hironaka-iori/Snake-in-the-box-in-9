# Geometric, incidence and spectral upper bounds

The strongest maintained theorem is **191 <= a(9) <= 236 edges** (`stronger/UpperBound236.lean`, see *Bound 236* below). It builds on the earlier unconditional intervals 191 <= a(9) <= 237 (`stronger/UpperBound237.lean`, see *Bound 237* below), 191 <= a(9) <= 238 (`stronger/UpperBound238.lean`, see *Bound 238* below) and 191 <= a(9) <= 241 (`stronger/UpperBound241.lean`, see *Bounds 242 and 241* below). The 191-edge witness is in the core project; the global 245-edge upper bound, on which the window bounds build, is in `stronger/UpperBound245.lean`. It combines endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive internal count-two vertices. A finite potential argument bounds the total singleton incidences, and the four-corner identity bounds the length. No search output is assumed. The earlier 247-, 248-, and 251-edge strengthenings are preserved. `EndpointFourWitness.lean` checks a 120-edge path attaining the endpoint estimate.

`SpectralUpperBound.lean` proves the upper bound 255 using the same `Snake9.Snake` definition as the core project. It imports mathlib's proof of Huang's degree theorem.

Required versions:

- Lean 4.19.0.
- mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Python 3.12 or later for the portable driver.

Prepare an existing mathlib checkout at the specified commit, with its dependencies and compiled cache available (`lake exe cache get` in that checkout). Put `lake` and the matching Lean tools on PATH. From the repository root run:

```sh
python work/spectral/verify_spectral.py --mathlib-dir /path/to/mathlib
```

The driver checks the dependency commit and compiler version, copies the current core `Snake9.lean` and the maintained sensitivity proof into a fresh ignored build directory, and checks all three modules. It does not alter the shared mathlib checkout. The final theorem audits must contain only the standard logical foundations.

The spectral theorem proves at most 255 edges. The stronger bound 254 is now proved in `SquareIncidence.lean`, using the core singleton-square lemma and finite-sum identities. It requires the same pinned mathlib checkout. From the repository root:

```sh
python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core
```

This driver checks the dependency version, rebuilds a fresh copy of all current core sources, and checks the incidence theorem. Omit `--fresh-core` to reuse the normal core build after running `lake build`. The fresh build is recorded in `outputs/incidence-reproduction.log`. The theorem audit must contain no `sorryAx` or custom axioms. The exact optimum remains unresolved.

The portable driver was run successfully for this checkpoint; see `outputs/spectral-portable-build.log` at the repository root.

## Reproduce the bound 245

With the same pinned dependency and toolchain, run from the repository root:

```sh
python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib
```

This driver always copies the current core sources and all 150 maintained strengthening modules into a fresh ignored directory, rebuilds the core, then checks the incidence and strengthening modules in dependency order. It clears inherited `LEAN_PATH`, so old research build products cannot satisfy imports. It checks the Lean version and mathlib commit, rejects modified tracked mathlib source, and saves each command, exit code, source SHA256, and compiler log in a manifest. All four strengthened intervals, the geometric exclusions including adjacent counts (1,3) and runs (2,2,2), endpoint bound and sharpness example, lower-bound witness, and general prefix theorem are audited transitively; only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The fresh source-only build succeeded for all 151 steps, including the core, incidence theorem, all 148 strengthening modules, and final theorem audits. Every recorded source hash was checked against the maintained source. The manifest and combined log are saved in `outputs/strengthened-reproduction-*` and `outputs/strengthened-245-reproduction-*`. The independent final import audit also passed.

`stronger/` is the authoritative strengthening source. Dated development directories are local research material and are not required or included in this PR. `ExactWedgeCount.lean` also proves the exact selected-wedge count and resulting defect identity, although the 251-edge theorem needs only the earlier upper estimate on wedges.

## Conditional 244 target

`Alpha223Potential.lean` and `Aggregate244Conditional.lean` are included in the reproduction driver. The no-(2,2,3) premise remains unproved. The original 151-step source-only build covers the unconditional 245 result. The PR integration audit separately checks these two additions against hash-matched compiled dependencies. A new complete driver run has 153 steps.

## Bounds 242 and 241 (unconditional)

- `WindowPotential242.lean` and `WindowPotential241.lean` use core Lean only and prove the sequence potentials.
- `AggregateWindowConditional.lean` proves `upper_242_of_certified_windows` and `upper_241_of_certified_windows`. Their window-exclusion premises are DRAT-certified for a local model, see `milestones/10-window-aggregate/`; the next items make them Lean theorems.
- A fresh 156-step run with `--core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget` succeeded. It is saved as `outputs/strengthened-window-reproduction-*`.
- `AggregateWindowUnconditional.lean` proves `upper_242_of_refuted` and `upper_241_of_refuted`. Their only hypothesis is `LocalWindow.AllRefuted`, the 22 statements `Refuted window bounds` of the local window certificates. The core module `final_lean/LocalWindowBridge.lean` moves each snake window to canonical position by a translation and a coordinate permutation, proves the abstract `Axioms` of `LocalWindowModel.lean` there, and selects the certificate from the direction shape. A window with directions 0,1,2,3,1 is read backwards. This module identifies `localAlpha` with the core count `coreAlpha`. When passing `--core-targets`, include `LocalWindowBridge`.
- `UpperBound241.lean` discharges `AllRefuted` with `LocalWindow.allRefuted` from the core module `final_lean/LocalWindowRefuted.lean` (clause soundness `LocalWindowSat/` plus the kernel-checked LRAT replays `LocalWindowUnsat/C*` through `LratCheck.lean`) and proves `upper_bound_242`, `upper_bound_241` and `verified_interval_191_241`. All three audit to `propext`, `Classical.choice`, `Quot.sound`: on macOS (`outputs/upper-bound-241-audit.log`) and from a fresh Linux environment with mathlib built from source (`outputs/upper-bound-241-audit-linux.log`). The core closure of `LocalWindowRefuted` has 1086 modules; `verify_strengthened.py` builds it through `work/guarded_lake_build.py`, which bounds the number of concurrent kernel checks and their memory. `Snake9.lean` itself peaks at about 7.4 GB on Linux, so the guard's per-module cap must be above that (`--core-rss-cap-gb`, default 9); choose `--core-heavy-jobs` as about (RAM in GB - 4) / 5.

## Conditional 239 and unconditional 238 (direction-aware automata)

`WindowAutomatonDefs/Data/Lemmas/Sequence/Bridge.lean` (core Lean) and `AggregateDirectionConditional.lean` (mathlib) prove `upper_239_of_direction_windows`: at most 239 edges if none of 145 certified direction-aware count windows occurs. `WindowAutomatonData.lean` is generated by `milestones/10-window-aggregate/scripts/gen_lean_automaton.py`; its `step_table` is checked by kernel evaluation. The five-centre variant (`WindowAutomaton5Data.lean`, 34 generated shard modules, `WindowAutomaton5Table/Sequence.lean`, `AggregateDirection238Conditional.lean`) proves `upper_238_of_direction_windows5` under 175 certified exclusions (pruned from 325; mean 7/2, potential range 10). All are included in the reproduction driver; the shards add about half an hour. Their fresh source-only run (`outputs/strengthened-direction-reproduction-*`) used the earlier 325-window tables; the regenerated 175-window chain was recompiled against the built core with `chain_audit.py` (`outputs/aggregate-238-chain-175-linux.log`, standard axioms only).

`AggregateDirectionUnconditional.lean` and `AggregateDirection238Unconditional.lean` reduce both premises to the certificate statements `AllRefuted239` and `AllRefuted238`, and `UpperBound239.lean` / `UpperBound238.lean` discharge them with the kernel replays of the LRAT refutations.

**Bound 238.** `UpperBound238.lean` proves `upper_bound_238` and `verified_interval_191_238`, so **238 is unconditional**. Both audit to `propext`, `Classical.choice`, `Quot.sound` only (`outputs/upper-bound-238-audit-linux.log`: `chain_audit.py --target UpperBound238`, Linux, Lean 4.19.0, mathlib c44e0c8e; `UpperBound238` took 163 s and 9.7 GB, the chain modules were reused from `outputs/aggregate-238-chain-175-linux.log`, 47 min, 34 shards at 3.4 GB). `AllRefuted238` is discharged by the core modules `LocalWindowDirSat5` (clause soundness of the 175 cores) and `LocalWindowDirUnsat5` (kernel replays of the 175 LRAT refutations: 14,206/14,206 modules, 0 failed; 2,803 check modules, 39.5 kernel-hours, at most 3.93 GB each; `LocalWindowDirUnsat5` itself 230 s, 7.63 GB; `outputs/upper-bound-238-replay-linux.log`). This audit was made on Linux only, against the incrementally built core; it is not a fresh source-only rebuild. `verify_strengthened.py --with-238` is that fresh reproduction path and has not been run yet: it copies the generated `LocalWindowUnsat/D*` modules, builds `LocalWindowDirUnsat5`, requires the 238 axiom audits and prints the bound actually proved.

**Bound 239.** It remains conditional: the 239 replays were stopped unfinished, since the unconditional 238 subsumes 239. `--with-239` builds `LocalWindowDirUnsat` instead, once its replays are generated. See `milestones/10-window-aggregate/README.md`.

## Radius-four windows: unconditional 237 and 236

The local model `Axioms` does not depend on the ball radius, so radius-four certificates pass through the same bridge. The generated chain `WindowAutomaton5R4bData/Shard0..33/Table/Sequence.lean`, `DirectionWindowBridge5R4b.lean`, `AggregateDirection237Conditional.lean` (`upper_237_of_direction_windows5R4b`) and `AggregateDirection237Unconditional.lean` (`upper_237_of_refuted`, premise `AllRefuted237` of the core module `final_lean/LocalWindowDirKeysR4b.lean`) compiles with standard axioms only (`outputs/aggregate-237-conditional-chain-linux.log`, `chain_audit.py --target AggregateDirection237Conditional`). The automaton uses 387 five-centre radius-four windows, pruned by `prune_costly.py --target-edges 237` from the 1351-window minimal set (mean 51/14, 6-bit potential of range 61: `51 m <= 14 sum + 336`, then `541 m <= 128730`), all DRAT-certified (`milestones/10-window-aggregate/data/direction_certificates_r4b.json`).

**Bound 237.** `UpperBound237.lean` proves `upper_bound_237` and `verified_interval_191_237`, so **237 is unconditional**. Both audit to `propext`, `Classical.choice`, `Quot.sound` only (`outputs/upper-bound-237-audit-linux.log`: `chain_audit.py --target UpperBound237`, Linux, Lean 4.19.0, mathlib c44e0c8e; `UpperBound237` itself took 97 s and 10.9 GB). `AllRefuted237` is discharged by the core modules `LocalWindowDirSatR4b` (clause soundness of the 387 cores, packed data) and `LocalWindowDirUnsatR4b` (kernel replays of the 387 LRAT refutations, all produced from the cores by a CaDiCaL portfolio, 289 M hints in total; replayed through `LratFast2`, with `LratFast2F` on segments of more than 2000 lemmas, and compiled with `lean` directly: 3,287 check modules, 34.0 kernel-hours, about 12 h (three runs) wall time; `outputs/upper-bound-237-replay-linux.log`). As for 238, this audit was made on Linux only, against the incrementally built core; a fresh source-only rebuild has not been carried out and `verify_strengthened.py` has no `--with-237` switch yet.

**Bound 236.** The full set of the radius-four refinement loop has 732 five-centre windows (14 window shapes; 371 shared with the 237 set; mean 42/11, 6-bit potential of range 48: `42 m <= 11 sum + 291`, then `427 m <= 101172`), pruned from the 1351-window minimal set by estimated LRAT cost so as to reuse the 237 windows, all DRAT-certified (`milestones/10-window-aggregate/data/direction_certificates_r4c.json`). Its chain `WindowAutomaton5R4Data/Shard0..33/Table/Sequence.lean`, `DirectionWindowBridge5R4.lean`, `AggregateDirection236Conditional.lean` (`upper_236_of_direction_windows5R4`) and `AggregateDirection236Unconditional.lean` (`upper_236_of_refuted`, premise `AllRefuted236` of `final_lean/LocalWindowDirKeysR4.lean`) compiles with standard axioms only (`outputs/aggregate-236-conditional-chain-linux.log`). `UpperBound236.lean` proves `upper_bound_236` and `verified_interval_191_236`, so **236 is unconditional**. Both audit to `propext`, `Classical.choice`, `Quot.sound` only (`outputs/upper-bound-236-audit-linux.log`: `chain_audit.py --target UpperBound236`, Linux, Lean 4.19.0, mathlib c44e0c8e; `UpperBound236` itself took 326 s and 12.7 GB). `AllRefuted236` is discharged by the core modules `LocalWindowDirSatR4` (packed clause soundness of the 732 cores; the 371 shared windows reuse the `Q*` modules of 237) and `LocalWindowDirUnsatR4` (kernel replays of the 732 LRAT refutations; the 361 new cores were produced by the CaDiCaL portfolio, 1.46 M core clauses; replayed through `LratFast2`, with `LratFast2F` on long segments, in 13- to 17-bit words, the largest window with 75 M hints needing 17-bit keys, and compiled with `lean` directly: 7,190 check modules, 100 kernel-hours, about three days of wall time; `LocalWindowDirUnsatR4` itself 382 s, 12.1 GB; `outputs/upper-bound-236-replay-linux.log`). The LRAT and generated data sources were deleted after compilation to save disk. As for 238 and 237, this audit was made on Linux only, against the incrementally built core; a fresh source-only rebuild has not been carried out and `verify_strengthened.py` has no `--with-236` switch yet.

## Low-singleton arm restriction

`LowSingletonArms.lean` proves the continuation restriction under explicit membership and internal-vertex premises. It does not prove the endpoint-proximity conjecture. Check it with the same pinned dependency:

```sh
python work/spectral/verify_incidence.py --module LowSingletonArms --mathlib-dir /path/to/mathlib
```

The separate radius-three forest certificate is part of the standard-library core. See `milestones/04-singleton-geometry/low_singleton_investigation.md` for scope and the distinction from a full connected snake.

## General cycle exclusion

`CycleExclusion.lean` checks that every nonempty finite subset of a snake has a vertex with at most one neighbor in the subset. It then checks all 41 recorded cycle cuts from the radius-five experiment. Reproduce with:

```sh
python work/spectral/verify_incidence.py --module CycleExclusion --mathlib-dir /path/to/mathlib
```

The finite Boolean contradiction is in the standard-library core project. Its complete connection to the normalized geometric model remains pending; see `milestones/06-radius-five/ball_certificate_investigation.md`.
