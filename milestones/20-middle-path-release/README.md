# Middle-path release and a fixed endpoint pair

Checkpoint: 20 October 2026. The construction target remains 196 edges.
No witness longer than 191 edges has been found.

## Growth from the two-arm seed

The milestone 19 seed has 186 edges and endpoints 67 and 41. The growth
driver releases coordinate faces, prioritizing those crossing both former
fixed coordinates, and rebuilds its model after each accepted improvement.
The one-edge growth run accepted lengths 187, 188, 189, 190 and 191. All
passed independent pairwise checks. No accepted change removed a vertex
of the original 142-vertex middle path. The final 191-edge path is equivalent
to bank entry 127 under cube symmetries and reversal.

The final pass returned 672 restricted exclusions at target 192. A separate
whole-cube search for 196, retaining at least 123 of the 187 original seed
vertices, returned UNKNOWN after 120 seconds. The middle was not frozen in
that direct model.

## Fixed endpoints and even increments

With endpoints 41 and 67, the length must be even: both endpoint words have
odd binary weight. Fixed-endpoint searches from the 186-edge seed for 188
edges returned INFEASIBLE on all 672 six-dimensional and 144 seven-dimensional
faces. These are restricted solver results without kernel certificates.

The endpoint pair itself does not prevent paths longer than 186: the 190-edge
prefix of the established Lean witness has endpoints 0 and 54. A coordinate
permutation with output-bit source order 0,1,3,2,6,4,5,7,8, followed by XOR 41,
maps these to 41 and 67. `lean/PairedSeed.lean` checks the transformation and
constructs this Snake 190 from the existing witness. No new axioms or native
evaluation are introduced.

`lean/EndpointParity.lean` proves that every snake with these endpoints has
even length. The existing `DfsParity.lean` was rebuilt into the local ignored
build directory. There are 16 successful theorem audits: ten for the paired
construction and transformation, four for the existing parity module, and
two for the specified endpoint pair.

| Fixed-endpoint experiment | Result |
|---|---|
| Reproduce the 190-edge witness | OPTIMAL, independently checked |
| Target 192, at most 32 deleted seed vertices | UNKNOWN, 120 seconds |
| Target 196, at most 64 deleted seed vertices | UNKNOWN, 120 seconds |

`data/paired-seed190.json` supplies the new control. The next construction
experiment should compare or recombine it with the 186-edge path, which has
the same endpoints, while checking cross-adjacencies. Endpoint parity is
only a necessary condition; it gives no existence claim at 196.

## Verification and reproduction

Run from the repository root using the established Python runtime:

```sh
python milestones/20-middle-path-release/scripts/paired_seed.py
python milestones/20-middle-path-release/scripts/grow.py --fixed-endpoints --step 2 --output milestones/20-middle-path-release/data/new-growth.json
python milestones/20-middle-path-release/scripts/fixed_search.py --edges 196 --removed 64 --output milestones/20-middle-path-release/data/new-fixed-search.json
python milestones/20-middle-path-release/scripts/verify.py
```

The initial one-edge growth used `scripts/snapshots/grow-v1.py`. The verifier
checks each accepted path, each replacement's scope, the bank match, the
paired witness transformation, solver witnesses, source hashes and all 16
Lean audits. It does not certify solver exclusions.

Compile from the pinned mathlib directory with Lean 4.19. Use the existing
dependency paths and prepend this milestone's ignored `build/` directory.
First compile `work/final_lean/DfsParity.lean` to `build/DfsParity.olean` using
its source directory as `--root`; then compile both maintained Lean files.
The saved successful logs are under `logs/`.

## Integration of collaborators' work

GitHub main advanced to `2883bc7b`, merging PR8 and the unconditional 241
proof. The local branch was fast-forwarded. The local .gitignore preference
to retain PDFs was preserved through stash `532a1543edce792f14ec4daa25c48d7a18d4488f`
and restored; the recovery stash remains available. No other local research
files were replaced. The incoming macOS and Linux source-build and final
axiom-audit receipts were inspected, along with the window model, complete
22-case refutation assembly and final upper-bound theorem. This round did
not rebuild that certificate closure.

The manuscript now states 191 <= a(9) <= 241 and includes a mathematical
outline of the discharged window premises. Historical proofs of 245 remain
as intermediate results. Bounds below 241 retain their conditional status.
The author block and local hyperlink settings are preserved.
