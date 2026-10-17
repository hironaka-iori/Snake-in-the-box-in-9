# Unconditional 244 project

Branch: `research/window-244`, created from main `537513d`.
The checked global interval remains **191..245**. Stage 2 is gated on the full
Stage-1 theorem, fresh source rebuild and transitive axiom audit.

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

## In progress

Split Boolean certificate compilation by `check_certificates.py`. Its lock
prevents duplicate starts. Status, module source/object/import hashes, timings
and peak private memory: `outputs/window244/certificate-build.json`.
Success has scope `PASSED_BOOLEAN_ONLY`. No geometric theorem follows yet.
Input structures split by 128 clauses, input lemmas by 64; RUP steps by 8.
Repeated part 102 exceeded the 1,800 MiB monitoring budget and is being split
into single-step modules. Stop and report if even individual steps cannot be
handled within the budget after reasonable decomposition.

## Remaining obligations (Stage 1)

1. Instantiate one parameterized assignment and connect all concrete clause
   families, auxiliary IDs and finite geometric facts to the generic proofs.
2. Instantiate the eligible-pair lists at each centre, connect terminal counts
   to alpha, and prove both standardized-window exclusions.
3. Normalize arbitrary five-vertex windows using translations and coordinate
   permutations; prove alpha invariance and cover repeated/distinct shapes.
   Add reversal invariance for `(3,2,2)`. Existing alpha-2-specific normalization
   cannot simply be used to discard the repeated shape here.
4. Finish both Boolean certificates under the memory budget.
5. Prove no-223, `upper_bound_244`, `verified_interval_191_244`.
6. Extend `verify_strengthened.py`, run a fresh source-only rebuild, audit final
   axioms, and then update all requested top-level and paper documentation.
7. Only after that consider the minimal-pattern Stage-2 search.

## Reproduction

From the repository root, with Python 3.12+:

```
python work/window244/audit_encoding.py
python work/window244/check_sequence_bounds.py
python work/window244/check_bridge.py --foundation-cache <prior-strengthened-build> --mathlib-dir <pinned-mathlib> --lake <Lean-4.19.0-lake>
python work/window244/check_certificates.py
```

The certificate driver currently locates the existing Windows Lean runtime in
the sibling research checkout; portability and the final clean rebuild driver
are still required. The foundation-cache check is a development convenience,
not a substitute for the required final source-only build. No new solver run
was performed in this checkpoint. Previously recorded certificates are treated
as untrusted inputs throughout.
