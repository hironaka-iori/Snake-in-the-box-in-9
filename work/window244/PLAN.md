# Unconditional 244 project

Branch: `research/window-244`, created from main `537513d`.
The checked global interval is **191..244**. Stage 1 completed on 18 October 2026.
Stage 2 may now begin; it is not part of this completed verification.

## Final verification

- `Snake9.no_two_two_three_internal` and `Snake9.no_three_two_two_internal`:
  `Window223Exclusion.lean`.
- `Snake9.upper_bound_244` and `Snake9.verified_interval_191_244`:
  `UpperBound244.lean`.
- Source-only build: **SUCCESS_191_244**, completed 2026-10-18 00:48 UTC.
  All 8,229 modules passed; all 9,103 source hashes and saved object/log hashes
  were rechecked. The final target axioms are only `propext`, `Classical.choice`,
  `Quot.sound`. Peak externally observed memory for the new modules was about
  1,716 MiB, within the 1,800 MiB monitoring budget.
- Versioned evidence: `outputs/window244/final-verification.json`,
  `final-reproduction-manifest.json`, `FinalAudit.log`, `source-build-logs.tar.gz`.
- The driver regenerates every emitted Lean source from preserved inputs;
  generated source hashes are in the manifest. No custom development objects
  are copied into the final build.
- No Stage-1 proof obligations remain. Exact optimality and Stage 2 remain open.

## Historical development checkpoints

The entries below describe development stages before the final audit. Their
pending/running statements are historical, not current status.

## Completed checkpoint

- Structural CNF audit, original LRAT replay, independent core RUP replay.
- Variable and clause-family map: `ENCODING.md`.
- Generic Lean cycle exclusion and endpoint geometry: `WindowGeometry.lean`.
- Generic endpoint and missing-counter clause families: `WindowCounters.lean`.
- Alpha equals the count of absent eligible corners, for any duplicate-free
  ordered pair list: `WindowAlpha.localAlpha_corner_list`.
- Development builds and axiom logs: `outputs/window244/bridge-build.json`,
  `outputs/window244/logs/Window*.log`. Imported custom foundation sources
  were hash-matched to this checkout. This is not the final fresh rebuild.
- Independent DP reproduced 245 and conditional 244. Bank entry 0 independently
  gives v=192, T=1682, E=1624 (406 empty squares), identity total 18428.
- `WindowClauses.lean` now supplies the numbered Boolean assignment, all generic
  clause families, constant simplification and the numbered-clause connection.
- `WindowReversal.lean` proves reversal invariance of alpha and the generic
  deduction of no-322 from a universal no-223 result.
- `WindowPermutation.lean` proves arbitrary coordinate-permutation invariance
  of adjacency, snakes and alpha. `CoordinateExtension.lean` extends the three
  or four window coordinates to a full coordinate permutation.
- `WindowNormalization.normalize_five_to_standard` covers **both** shapes for
  every five-vertex window and preserves alpha at every path index.
- Representative concrete endpoint-counter, missing-counter, exact-count and
  cycle clause blocks passed early kernel checks (`geometry-family-smoke.json`).

## In progress

An independent source-only reconstruction is now running in
`work/spectral/.verification/window244-i53n2a5_/`; its `manifest.json` is the
authoritative state of that build. Output streams are
`outputs/window244/fresh-rebuild.stdout.log` and `fresh-rebuild.stderr.log`.
It imports no custom development objects. The build has its own lock and
records the driver hashes as well as source, object, dependency and log hashes.
If it fails, correct the reported proof obligation and resume that directory;
do not interpret a running manifest as a successful theorem audit.

The assembly from the two standardized contexts to arbitrary internal indices
also passed an isolated conditional development probe (`AssemblyProbe.log`).
Its two explicit hypotheses are still to be discharged by the complete concrete
geometry and refutations. This probe is not the unconditional exclusion.

Split Boolean certificate compilation by `check_certificates.py --shape repeated`
and `--shape distinct`, with separate locks and checkpoints. Status, module
source/object/import hashes, timings and peak private memory are in
`outputs/window244/certificate-{shape}-build.json`; the combined report is
written only after both have passed. The old combined runner was stopped at
its saved checkpoint before these independent shape jobs were launched.
Success has scope `PASSED_BOOLEAN_ONLY`. No geometric theorem follows yet.
Input structures split by 128 clauses, input lemmas by 64; RUP steps by at most
8, further subdivided by hint count. Repeated part 102 passed after single-step
splitting; subsequent large groups use a 200-hint budget. The largest single
hint trace in each shape independently passed, at about 1.3--1.4 GiB private
memory. Concrete geometry blocks are split into groups of eight clauses after
an initial 32-clause group exceeded the monitoring budget.

## Remaining obligations (Stage 1)

1. Complete all concrete clause-instance checks generated by `generate_bridge.py`.
   Its model, core and module prefix are parameters; the model supplies the
   shape, radius and positive alpha triple. Finite facts are checked by Lean.
2. Finish both Boolean certificates under the memory budget.
3. Compile the already written integration sources `Window223Exclusion.lean`
   and `UpperBound244.lean` once their generated imports are available. These
   files are **not yet checked final theorems** merely because they exist.
4. Run the implemented `verify_strengthened.py --window244` fresh source-only
   rebuild (resumable with `--resume-build`), audit final
   axioms, and then update all requested top-level and paper documentation.
5. Only after that consider the minimal-pattern Stage-2 search.

## Reproduction

From the repository root, with Python 3.12+:

```
python work/window244/audit_encoding.py
python work/window244/check_sequence_bounds.py
python work/window244/check_bridge.py --foundation-cache <prior-strengthened-build> --mathlib-dir <pinned-mathlib> --lake <Lean-4.19.0-lake>
python work/window244/check_certificates.py --shape repeated
python work/window244/check_certificates.py --shape distinct
python work/window244/build_geometry.py --shape repeated
python work/window244/build_geometry.py --shape distinct
python work/spectral/verify_strengthened.py --window244 --mathlib-dir <pinned-mathlib>
```

The certificate driver currently locates the existing Windows Lean runtime in
the sibling research checkout. The final clean rebuild driver uses the Lean
toolchain on PATH. The foundation-cache check is a development convenience,
not a substitute for the required final source-only build. No new solver run
was performed in this checkpoint. Previously recorded certificates are treated
as untrusted inputs throughout.
