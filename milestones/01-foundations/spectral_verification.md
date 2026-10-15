# Global nine-dimensional bound

`SpectralUpperBound.lean` proves, for the same `Snake9.Snake` type as the checked witness:

```lean
theorem universal_upper_bound_255 {m : Nat} (p : Snake m) : m ≤ 255
theorem verified_bounds : Nonempty (Snake 191) ∧
    (∀ m, Nonempty (Snake m) → m ≤ 255)
```

The proof imports the maintained Lean proof of Huang's degree theorem from mathlib's `Archive/Sensitivity.lean`. It proves injectivity of the map from integers below 512 to their nine bits, decodes every cube adjacency back to the original path relation, and bounds the induced degree by two. Huang's theorem excludes 257 selected vertices, hence 256 edges.

This is a standard consequence of Huang's theorem, now checked for the witness definition used in this investigation. It does not prove the conjectured optimum 196 or the competing optimum 191.

The checked environment is Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The archive source was compiled in this investigation. The theorem audit in `spectral-build.log` lists only `propext`, `Classical.choice`, and `Quot.sound`.

The core project uses only the standard library. For this repository, follow `work/spectral/README.md` and its portable verification driver. The following archive notes describe an earlier local checkpoint. The separate `snake9_spectral_project.zip` adds the mathlib-dependent theorem and a pinned Lake configuration. With Lean 4.19.0 installed, the portable reproduction commands are:

```text
lake update
lake exe cache get
lake build
```

The proof sources were checked against the existing pinned local mathlib installation. The packaged archive was then extracted into a fresh project directory, and `build_with_existing_mathlib.ps1` successfully recompiled the archive theorem, the 191-edge witness module, and the global-bound module from their sources. `spectral-reproduction.log` records that successful run. The fresh online dependency-installation commands are provided for reproduction and have not been rerun in a clean machine.
