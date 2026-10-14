# Spectral upper bound

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

The checked theorem proves at most 255 edges. It does not certify the manuscript's stronger written bound of 254, whose global incidence proof is still pending. See the root collaborator handoff.

The portable driver was run successfully for this checkpoint; see `outputs/spectral-portable-build.log` at the repository root.
