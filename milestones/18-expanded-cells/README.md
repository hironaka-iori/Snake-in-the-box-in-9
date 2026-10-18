# Expanded cells and bank alignment

Checkpoint: 19 October 2026. Construction target: a 196-edge induced path.
No witness longer than 191 edges has been found.

## Alignment diagnosis

Milestone 17 identified the four-connector palette as too restrictive.
This milestone allows every vertex of Q9, with an optional budget on the
number selected outside that palette.

The alignment search examines 126 choices of five internal coordinates,
120 internal coordinate orders, 32 internal translations and two outer
translation parities. Outer coordinate permutations and even outer
translations leave palette membership unchanged. There are 967,680 raw
representatives; each coordinate set has 960 distinct palette patterns
after duplicate removal. All 131 published bank witnesses are scored.

| Minimum outside vertices | Bank witnesses |
|---:|---:|
| 29 | 2 |
| 30 | 2 |
| 35 | 3 |
| 36 | 57 |
| 37 | 63 |
| 38 | 4 |

Bank entry 129 is the selected seed. Its 29 outside vertices calibrate the
search budget; they do not establish a minimum for arbitrary snakes.
All transformed paths pass independent pairwise adjacency checks.

## Lean-checked transformation

The selected map assigns source bits 1,5,4,2,7,0,3,6,8 to output bits
0 through 8, then XORs by 7. `lean/Alignment.lean` checks its inverse and
coordinate-flip identities, derives injectivity and adjacency equivalence,
and constructs a snake of the same length from any snake. Seven audits pass
with only standard axioms. The finite bank-wide optimization is not a Lean
completeness result.

## Searches and controls

| Experiment | Result |
|---|---|
| Fixed 191-edge seed, outside budget 29 | Reproduced |
| Same fixed seed, outside budget 28 | Rejected |
| Target 196, at most 32 seed deletions, outside budget 34 | UNKNOWN, 120 seconds |
| Target 192, at most 16 deletions, outside budget 40 | UNKNOWN, 120 seconds |
| Target 192, at most 16 deletions, no effective palette budget | UNKNOWN, 120 seconds |
| Replace one Q5 cell, target 192 | 16 restricted INFEASIBLE results |
| Replace adjacent two-cell region, target 192 | 32 restricted INFEASIBLE results |
| Replace one cell, target 191 | Feasible control |
| Distinct 191-edge vertex set in cells 0 and 2 | Feasible; equivalent to bank entry 127 |

The neutral rearrangement removes one vertex and adds one. Canonical
transition sequences compare paths under translations, coordinate
permutations and reversal. It differs from entry 129 but recovers an existing
class. No new bank class or length record follows.

The cell repairs fix all selected and unselected vertices outside the
released cells. The solver exclusions have no Lean infeasibility
certificates and do not cover other coordinate partitions or larger repairs.

## Reproduction

Run from the repository root with the pinned Python runtime and installed
OR-Tools dependencies:

```sh
python milestones/18-expanded-cells/scripts/align_bank.py
python milestones/18-expanded-cells/scripts/make_alignment_certificate.py
python milestones/18-expanded-cells/scripts/search.py --edges 196 --removed 32 --outside 34 --output milestones/18-expanded-cells/data/new-search.json
python milestones/18-expanded-cells/scripts/repair_cells.py --cells 2 --edges 192 --output milestones/18-expanded-cells/data/new-repair.json
```

Compile `lean/Alignment.lean` with Lean 4.19 from the pinned mathlib working
directory and the same dependency paths as milestone 17. The maintained
certificate uses direct bit expressions and has a successful fresh
compilation receipt in `logs/alignment.log`.

Then run `scripts/verify.py`. It checks all 131 aligned witnesses,
the solver witnesses and recorded repair scopes, source hashes, the neutral
comparison, and all seven Lean audits. It does not certify solver UNSAT or
bank-optimization completeness. `scripts/snapshots/repair-cells-v1.py`
preserves the version used for the first 48 repair experiments.

## Next construction step

Change the coordinate partition or resynthesize connections across more
than two cells. The current fixed-partition two-cell searches found no
192-edge improvement, and the first neutral move stayed within the known
bank. These results guide where to enlarge the search; they do not justify
an optimality claim. Global upper-bound research remains with collaborators.
