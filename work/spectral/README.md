# Geometric, incidence and spectral upper bounds

The strongest maintained theorem is **191 <= a(9) <= 245 edges**. The 191-edge witness is in the core project; the global 245-edge upper bound is in `stronger/UpperBound245.lean`. It combines endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive internal count-two vertices. A finite potential argument bounds the total singleton incidences, and the four-corner identity bounds the length. No search output is assumed. The earlier 247-, 248-, and 251-edge strengthenings are preserved. `EndpointFourWitness.lean` checks a 120-edge path attaining the endpoint estimate.

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

## Conditional 242 and 241 targets

- `WindowPotential242.lean` and `WindowPotential241.lean` use core Lean only and prove the sequence potentials.
- `AggregateWindowConditional.lean` proves `upper_242_of_certified_windows` and `upper_241_of_certified_windows`. Their window-exclusion premises are DRAT-certified for a local model, see `milestones/10-window-aggregate/`, but they are not Lean theorems.
- A fresh 156-step run with `--core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget` succeeded. It is saved as `outputs/strengthened-window-reproduction-*`.
- A 239-step run (`outputs/strengthened-direction-k6-reproduction-manifest.json`) covers the direction-aware chains for 239, 238 (`WindowAutomatonK5R3*`, regenerated with the fast kernel loop) and 235 (`WindowAutomatonK6R3*`, 2,635 certified windows). `--build-dir DIR` reuses a build directory: modules whose object is newer than their source and whose earlier check succeeded are skipped, so a run survives machine restarts; the manifest marks such steps `cached`.

## Conditional 239 target (direction-aware automaton)

`WindowAutomatonDefs/Data/Lemmas/Sequence/Bridge.lean` (core Lean) and `AggregateDirectionConditional.lean` (mathlib) prove `upper_239_of_direction_windows`: at most 239 edges if none of 145 certified direction-aware count windows occurs. `WindowAutomatonData.lean` is generated by `milestones/10-window-aggregate/scripts/gen_lean_automaton.py`; its `step_table` is checked by kernel evaluation. The five-centre variant (`WindowAutomatonK5R3Data.lean`, 34 generated shard modules, `WindowAutomatonK5R3Table/Sequence.lean`, `AggregateDirectionK5R3Conditional.lean`) proves `upper_238_of_direction_windowsK5R3` under 325 certified exclusions. The six-centre variant (`WindowAutomatonK6R3*`, generated by `gen_lean_automaton_k.py`, on the kernel-loop primitives of `WindowAutomatonLoop.lean`: a body-first `Nat.rec` loop, `letN` to re-enter a computed table window as a numeral, and `Nat.testBit` transport lemmas) proves `upper_235_of_direction_windowsK6R3` under 2,635 certified exclusions. All are included in the reproduction driver; the 34 six-centre shards take about ten minutes on three cores.

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
