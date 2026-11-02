# Milestone 88: rejection boxes and a checked coverage pilot

The generic rejection-box argument and its first concrete coverage certificate
pass Lean 4.19. This round has **26 theorem audits**. For direction 0 and
history 0, Lean checks 375 rule witnesses and a six-way coverage tree, then
proves that every bounded code passing numeric retention is accepted by the
recorded membership diagram. This is one context; complete coverage of all
791 compatible contexts remains open.

The maintained project interval is 191 through 235 edges. The 235 upper bound
uses the inspected contributor theorem and saved audit, without a new full
independent rebuild. The target 234 remains conditional. This milestone does
not improve either numerical bound.

## Argument

A count box is a product of six inclusive integer intervals in 1 through 6.
A rule witness certifies that every vector in that box triggers an existing
exclusion. A coverage tree partitions the six-symbol domain until every
remaining branch is either accepted by the membership diagram or contained
in a witnessed box. Since a retained code avoids every witnessed box, it
must be accepted by the diagram.

The [mathematical note](mathematical-note.md) gives the definitions and proof
structure. The generic result needs concrete witness and coverage equations.
Those equations are now checked for the direction-0/history-0 pilot.
Its specialization to actual snakes retains the two earlier reference-catalogue
premises, `AllRefuted6K235` and `AllRefuted236`.

| Module | Theorem audits | Checked content |
| --- | ---: | --- |
| `Boxes` | 2 | Box membership and prefix containment |
| `DigitReconstruction` | 5 | Six-digit reconstruction and slice encoding |
| `BoxWitness` | 8 | Reference, short, interval and history witnesses imply rejection |
| `CoverTree` | 4 | Complete six-way coverage and membership implication |
| `CoverageAssembly` | 4 | Numeric retention and conditional actual-snake specialization |
| `Case000Checks` | 3 | All pilot witnesses, its cover equation and retained-code theorem |

`GraphData` and `Case000Data` also compile successfully. They are data modules,
with no printed theorem audits. The pilot's three checks took 92.594 seconds;
its data modules took 96.219 and 46.203 seconds respectively. The coverage
equation has no axioms; other printed results use only subsets of
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or
`native_decide` occurs in these eight sources. Existing inherited proof
objects are reused; their complete dependency closure was not rebuilt.

## Computational compression

The exact box reconstruction matches all 505 base directions and three
history modifications, all 791 compatible blocks, and 4,947,008 saved rows.
All 37,084 incompatible blocks are empty. This is a computational comparison,
distinct from the one concrete Lean pilot.

Maximum-uncovered greedy selection followed by redundancy deletion keeps
356,548 direct box occurrences. Each selected direct box has a private code
within its final cover, so that cover is irredundant. No minimum-size claim
is made. The earlier descending-volume baseline keeps 357,917 occurrences.
Both data sets, their exact generator versions, and initial failure diagnostics
are preserved.

More significantly, all 127 membership classes admit an exact common cover
using box geometries available in every context of that class. The pruned
common covers contain 82,659 class-box occurrences. This supports 127 shared
geometric checks once the context-specific witnesses have been materialized
and checked. The saved class payload contains example witnesses, not a
complete witness list for every context. See the [construction audit](audit/box-cover.md).

The pilot has 723 distinct tree nodes, 11,869 expanded node visits, and 6,123
accepted codes out of 46,656. Its generation receipt records the earlier
pending stage. The later [Lean receipt](data/Case000Checks-audit.json) and
[proof summary](data/proof-summary.json) record successful validation.

## Reproduction and saved evidence

Use the pinned Lean 4.19 environment recorded in the check scripts and receipts.
From this folder, the dependency order is:

```text
python scripts/check_witness.py Boxes
python scripts/check_witness.py DigitReconstruction
python scripts/check_witness.py BoxWitness
python scripts/check_cover.py CoverTree
python scripts/check_coverage_assembly.py
python scripts/check_certificate.py GraphData
python scripts/check_certificate.py Case000Data
python scripts/check_certificate.py Case000Checks
```

The current generator is `python scripts/build_boxes.py --max-gain`.
The baseline source is preserved as text plus its original line-ending rule
in `data/box-cover-baseline-source.json`. `build_pilot.py` regenerates the pilot
data and performs a complete Python replay before the Lean checks.
Generation alone does not establish any Lean result. Do not regenerate data
while a checker is using it.

`python scripts/verify_saved.py --verify` checks the exact saved-file manifest.
`--staged` additionally checks Git's staged bytes. `finalize.py` verifies owned
source, object and log hashes and records a delta snapshot of the existing
case7302 replay. It reuses earlier object hashes for previously observed
successful modules, while hashing new objects. The prior checkpoint is pinned.
The [checkpoint](data/checkpoint.json) and [manifest](data/file-manifest.json)
identify this round's evidence and shared handover versions.

## Remaining work

1. Generate all 127 shared geometric certificates and each context's rule
   witnesses. Check them in measured, sequential batches, reusing the generic
   theorem and the existing diagram data.
2. Identify diagram acceptance with the recorded full-key rows, and certify
   both endpoint columns. Full edge keys must be preserved because some
   endpoint pairs have two differently indexed edges.
3. Discharge the two reference-catalogue premises, interpret every credit,
   complete the remaining local share proofs, and replay the full potential.

The existing case7302 driver remains the only replay process for that case.
Its snapshot is partial progress, without a completed local-share theorem.
Inspect its actual process and final audit before any restart. The manuscript
remains revision 86; the next full revision is scheduled for milestone 96.
