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

This driver always copies the current core sources and all 148 maintained strengthening modules into a fresh ignored directory, rebuilds the core, then checks the incidence and strengthening modules in dependency order. It clears inherited `LEAN_PATH`, so old research build products cannot satisfy imports. It checks the Lean version and mathlib commit, rejects modified tracked mathlib source, and saves each command, exit code, source SHA256, and compiler log in a manifest. All four strengthened intervals, the geometric exclusions including adjacent counts (1,3) and runs (2,2,2), endpoint bound and sharpness example, lower-bound witness, and general prefix theorem are audited transitively; only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The fresh source-only build succeeded for all 151 steps, including the core, incidence theorem, all 148 strengthening modules, and final theorem audits. Every recorded source hash was checked against the maintained source. The manifest and combined log are saved in `outputs/strengthened-reproduction-*` and `outputs/strengthened-245-reproduction-*`. The independent final import audit also passed.

`stronger/` is the authoritative strengthening source. The dated research directories contain frozen development snapshots and exploratory results. `ExactWedgeCount.lean` also proves the exact selected-wedge count and resulting defect identity, although the 251-edge theorem needs only the earlier upper estimate on wedges.
