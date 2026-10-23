# Three-square empty-share bonus

Research date: 23 October 2026. This follows the empty-square route and the sharpness witnesses from milestone34. The original equality-case target is proved with a weaker hypothesis: no singleton-count equality is required.

For seven consecutive transitions `(a,b,c,d,e,b,f)` with six distinct coordinates, let `x` and `y` be the first and sixth internal vertices. Then

- The two M12 empty-square shares sum to at least 12.
- Their singleton counts sum to at least 9 by milestone33, so their combined charge is at least 228.
- For any set of N qualifying occurrences in one snake, the total share is at least 6N. Each position belongs to at most two charged pairs.

These statements are checked in Lean for arbitrary snakes and coordinate labels. No improvement to the integrated interval `191 <= a(9) <= 238` follows yet. The share constant 12 is not asserted to be sharp, and a positive frequency of qualifying patterns has not been proved.

## Geometric explanation

The internal path vertices already have their two selected neighbors. Their other neighbors are absent. This forces three empty coordinate squares. At four neighbors of the charged pair, those squares supply empty-square counts 1,2,2,1. Each of these neighbors has at most six selected neighbors. Their integer share contributions are therefore at least 2,4,4,2.

The extracted certificate uses only the segment and the selected-vertex degree restriction. It contains no count-counter clause and no cycle cut. The result also holds for selected sets containing cycles; it cannot alone remove the cycle obstruction to purely local methods. The same geometric enumeration supports pattern 0123410, but the new arbitrary-snake Lean wrapper in this milestone concerns 0123415.

## Verification

Thirteen axiom audits cover the general share checker, clause interpretation, pinned geometric share bridge, arbitrary-snake share and charge inequalities, and overlap accounting. All use only `propext`, `Classical.choice`, and `Quot.sound`. No unchecked native reduction is used.

The initial exact-quotient model excludes share sum at most 11 when the count sum is 9. An independently tagged encoding gives a 115-clause core on 114 active variables. Its 281-reference LRAT refutation passes Lean. Inspection of the core removes the count-sum assumption: the Lean clause interpretation uses an empty counter list. Both encoders accept the complete 138-edge sharpness witness, with pair shares 25 and 17, as a positive control at cap 42.

The share bridge is pinned to contributor commit `d4936d720e8a54011e6adaff598fec5bb86fd515`; `data/upstream.json` records its path and hash. This integrates one checked component from that branch, without importing its pending global bound.

## Reproduction

Use Lean 4.19.0 and the existing pinned mathlib environment. The PowerShell build scripts refer to the local support builds from milestones28,31,32,33; they are incremental and do not claim a clean-checkout rebuild of the entire project.

1. `scripts/probe.py`, `scripts/control.py`, and `scripts/geometry.py` reproduce independent numerical and geometric controls.
2. `scripts/archive.py --unpack` restores the raw certificates. `scripts/certificate.py` regenerates the numerical proof, and `scripts/export.py` generates the Lean clauses and replay.
3. `scripts/build.ps1`, then `scripts/check.ps1`, check all new modules in fresh build directories.
4. `scripts/archive.py --pack` records lossless certificate hashes. `scripts/verify.py` checks provenance, proof receipts, source hashes, archives, and controls. The result is `data/verification.json`.

The paper and the existing editor source are synchronized. The built-in preview compiler failed before TeX because the Windows restricted-token runner cannot enforce the split writable roots. The current PDF has not been verified.

## Next direction

Retain occurrence count in the low-charge sequence analysis, and combine the new pair shares with existing window shares under one capacity constraint per vertex. Adding both bonuses without accounting for shared positions would double-count the same resource. Establish occurrence frequency or an appropriate finite-state potential before claiming a global improvement. A stronger equality-conditioned share bound can also be tested, since the count-only sharpness witnesses have share sum 42 and the current proof gives 12.
