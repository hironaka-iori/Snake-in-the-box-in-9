# Joint six-count restrictions on three direction shapes

The combined floors 26 on $0123042$ and 25 on each of $0120310$ and $0123024$
leave both finite-graph means and integer comparisons unchanged. The original
milestone-121 attaining cycles avoid all three shapes. Consequently every
componentwise stronger choice of these three floors has the same exact graph
means. No further strength sweep was run.

## Computation and evidence

The producer reconstructed the milestone-121 removal set and reproduced both
complete retained-weight hashes before applying the new restrictions. It kept
the inherited thirteen count-sum rules and coefficient 24 unchanged. For a
matching seven-direction suffix, new credit is allowed only when the first
chronological clipped count is below 6. The credit equals 24 times the positive
part of the proposed floor minus the sum of the six clipped counts. The shared
bonus is the maximum of this credit and the existing bonus.

Reversal is used to recognize the direction shape. It does not reverse the
chronological guard or transfer credit to a different set of five positions.
Symbol 6 retains its full interval $[6,21]$. New deletion requires all six
symbols below 6 and their exact sum below the proposed floor.

| Canonical shape | Proposed floor | Newly deleted keys | Retained keys with increased credit |
| --- | ---: | ---: | ---: |
| $0123042$ | 26 | 4,609 | 19,310 |
| $0120310$ | 25 | 316 | 1,096 |
| $0123024$ | 25 | 5,157 | 21,356 |
| Total | | 10,082 | 41,762 |

The resulting graph has 1,601,856 states and 4,673,032 retained edges. The
producer checked every retained-edge potential inequality in both profiles,
using the saved milestone-121 potentials. The original eighteen-cycle and
four-cycle respectively remain and attain those potentials' means.

| Profile | Exact mean | Feasible potential range | Comparison | Integer comparison |
| --- | ---: | ---: | ---: | ---: |
| Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |

These potential ranges were checked, without a new range minimization. The
subsequent saved-data audit checks every pinned input, the removal-set relation,
cycle directions/counts/weights against milestone 121, cycle chaining, potential
file hashes and ranges, equality on cycle edges, exact comparison arithmetic,
and absence of the three target shapes. It does not independently reconstruct
the full graph or rerun Lean.

The initial full-Q9 probe for $0123024$ at cap 24 returned
`UNSAT_UNCERTIFIED` in 23.531 seconds with zero cycle cuts. The corresponding
$0120310$ probe returned `UNKNOWN` after 30.140 seconds with zero cycle cuts.
These two files are pinned in the saved-data audit. The retained floor 26 on
$0123042$ has the earlier milestone-123 resumed native negative evidence.
All three local floors remain explicit premises in this experiment; `UNKNOWN`
supplies no floor. The generic guarded-charge Lean statements passed in
milestone 123, while local floor proofs, inherited count-sum hypotheses,
application to this full graph, and global assembly remain separate.

## Why larger floors on these shapes cannot help

Increasing any of the three floors can only increase retained-edge weights or
delete additional matching keys. Both saved attaining cycles contain no
matching key, so all their edges and weights remain unchanged. The checked
potentials remain feasible, while the cycles still attain their means. This
establishes the exact same means for every componentwise larger floor.

Even allowing potential range zero gives

$$
\frac{1323416}{5623}>235,
\qquad
\frac{137866}{587}>234.
$$

Thus no stronger floor on these three shapes, or improvement of potential
range alone, can improve the displayed integer comparisons. The conditional
four-cycle contains two endpoint events; this experiment does not establish
an obstruction to all possible endpoint credits.

## Surviving cycle contexts

The following counts retain chronological order. Canonical shapes identify a
word with its reversal. A displayed 6 is a clipped interval symbol.
`data/graph-26-25-25/cycle-targets.json` also saves both direction orientations,
canonical count order, and the first floor that changes deletion or credit.

| Profile | Edge | Canonical seven-direction shape | Six chronological symbols | Sum |
| --- | ---: | --- | --- | ---: |
| Completed | 3360987 | $0120340$ | $(2,3,6,3,6,4)$ | 24 |
| Completed | 1609403 | $0123104$ | $(3,6,3,6,4,2)$ | 24 |
| Completed | 241712 | $0123104$ | $(6,3,6,4,2,5)$ | 26 |
| Completed | 3577410 | $0120342$ | $(3,6,4,2,5,2)$ | 22 |
| Completed | 1719625 | $0123014$ | $(6,4,2,5,2,4)$ | 23 |
| Completed | 463685 | $0123014$ | $(4,2,5,2,4,6)$ | 23 |
| Completed | 2941505 | $0120342$ | $(2,5,2,4,6,3)$ | 22 |
| Completed | 934679 | $0123104$ | $(5,2,4,6,3,6)$ | 26 |
| Completed | 1332711 | $0123104$ | $(2,4,6,3,6,3)$ | 24 |
| Completed | 3490529 | $0120340$ | $(4,6,3,6,3,2)$ | 24 |
| Completed | 1620155 | $0123104$ | $(6,3,6,3,2,6)$ | 26 |
| Completed | 230938 | $0123104$ | $(3,6,3,2,6,3)$ | 23 |
| Completed | 3364935 | $0120340$ | $(6,3,2,6,3,6)$ | 26 |
| Completed | 1608593 | $0123104$ | $(3,2,6,3,6,2)$ | 22 |
| Completed | 208356 | $0123104$ | $(2,6,3,6,2,3)$ | 22 |
| Completed | 3365083 | $0120340$ | $(6,3,6,2,3,6)$ | 26 |
| Completed | 1609336 | $0123104$ | $(3,6,2,3,6,3)$ | 23 |
| Completed | 212865 | $0123104$ | $(6,2,3,6,3,6)$ | 26 |
| Conditional | 2222588 | $0120324$ | $(5,5,3,3,5,5)$ | 26 |
| Conditional | 148850 | $0120324$ | $(5,3,3,5,5,3)$ | 24 |
| Conditional | 2219941 | $0120324$ | $(3,3,5,5,3,3)$ | 22 |
| Conditional | 146842 | $0120324$ | $(3,5,5,3,3,5)$ | 24 |

For the conditional cycle, a floor of 23 on the single shape $0120324$ would
remove edge 2219941, and floor 25 would additionally remove both sum-24 edges.
The forward forms $0123143$ and $0120314$ both reverse to this same canonical
shape. Earlier forward-only descriptions should not be interpreted as distinct
targets.

For the completed cycle, a floor of 23 on $0120342$ or $0123104$ would increase
the credit on its corresponding sum-22 contexts whose first symbol is exact.
Those keys contain symbol 6, so this change would provide credit rather than
the exact-count deletion used above. These are priorities for further tests;
no new local floor or actual-snake realization of these cycles is asserted.

## Saved outputs

No SAT solver, Lean compiler, or additional graph sweep was launched by this
worker. All files from milestone 123 remain unchanged. This experiment
establishes finite-graph conclusions under stated premises and supplies no new
unconditional bound on snakes.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_six_shapes.py` | `066b117d63f3d6cf78341073fa7b7a09dd39946a7f4b77961bf71b23114e782f` |
| `data/graph-26-25-25/results.json` | `d3b3c248c4fd14491d444413f18e9a8b5768f12849945ded16afcc44412d9f1a` |
| `data/graph-26-25-25/saved-cycle-audit.json` | `e99c16531c6cfa8fda28a187cc75dca6ce5e5c26aef45a28d806a83a91623cfd` |
| `data/graph-26-25-25/cycle-targets.json` | `9d5bf150fca0903496cd1a4e1b55d37457176699477f634b242c500d3adf00c4` |
