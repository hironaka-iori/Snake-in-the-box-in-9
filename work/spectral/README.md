# Incidence and spectral upper bounds

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

## Low-singleton arm restriction

`LowSingletonArms.lean` proves the continuation restriction under explicit membership and internal-vertex premises. It does not prove the endpoint-proximity conjecture. Check it with the same pinned dependency:

```sh
python work/spectral/verify_incidence.py --module LowSingletonArms --mathlib-dir /path/to/mathlib
```

The separate radius-three forest certificate is part of the standard-library core. See `outputs/low_singleton_investigation.md` for scope and the distinction from a full connected snake.

## General cycle exclusion

`CycleExclusion.lean` checks that every nonempty finite subset of a snake has a vertex with at most one neighbor in the subset. It then checks all 41 recorded cycle cuts from the radius-five experiment. Reproduce with:

```sh
python work/spectral/verify_incidence.py --module CycleExclusion --mathlib-dir /path/to/mathlib
```

The finite Boolean contradiction is in the standard-library core project. Its complete connection to the normalized geometric model remains pending; see `outputs/ball_certificate_investigation.md`.
