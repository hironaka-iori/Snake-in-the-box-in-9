# Short-walk obstruction to weakening the share catalogue

The six pending shape rules cannot simply be omitted from the current conditional
234 argument and compensated for by a different constant slope or potential.
This conclusion concerns the exact relaxed graph and the present boundary budget.
It does not exclude stronger geometric restrictions or a better snake bound.

## Argument

Let an edge of weight \(w\) from \(u\) to \(v\) satisfy
\[
p+\pi(v)\le w+\pi(u),\qquad \max\pi-\min\pi\le R.
\]
The current boundary calculation excludes a 235-edge snake only when
\[
227p-R>111960.
\]
Every tested relaxation retains a directed cycle of length three and total weight
1488. Summing its potential inequalities gives \(p\le496\).

Suppose the same graph contains a directed walk of length \(L\le227\), total
weight \(W\), and deficit \(D=496L-W\ge632\). Summing along that walk gives
\(pL-W\le R\). Therefore
\[
227p-R\le(227-L)p+W
\le(227-L)496+W
=112592-D\le111960.
\]
The required strict inequality is impossible. The argument allows arbitrary real
potentials and slopes; its rational specialization is checked in
`../lean/PotentialRangeObstruction.lean`. The integer-scaled certificates used in
this project fall within that specialization.

## Exact witnesses

Each row changes only the indicated floor, while keeping the other eight floors
of the mixed catalogue and all previous graph rules. The original floor is 20
for 012034, 12 for 012310, and 16 for the other shapes. Floor zero removes the
extra count-free credit; it retains any older credit already in the graph.

| Shape | Weakened floor | Walk length | Deficit |
|---|---:|---:|---:|
| 012301 | 0 | 12 | 635 |
| 012032 | 0 | 11 | 641 |
| 012034 | 0 | 7 | 636 |
| 012310 | 0 | 17 | 636 |
| 012340 | 0 | 7 | 632 |
| 012345 | 12 | 12 | 632 |

The weaker share-12 theorem for 012345 is already checked, so that test retains
it. All walks, their edge indices, state endpoints, direction IDs, counts,
history IDs and weights are in `data/catalogue-tests.json`. Each individual
test also has its own JSON file. Source array hashes identify the exact graph.

The discovery calculation performs bounded shortest-walk relaxation from every
state. A separate verification invocation reloads the source arrays, reconstructs
every changed weight, and checks the saved walks and cycle directly. It does
not rely on the discovery distances or predecessor data. All six checks passed.
The finite array checks use Python; their full Lean replay remains unperformed.

## Interpretation and limits

This strengthens milestone73's fixed-potential minimality test: changing the
potential or its constant slope cannot rescue these six specified relaxations.
The result does not say that every numerical floor is least possible after
reoptimization. In particular, lowering a floor by one was not tested here.
It also does not show that a witness walk extends to an actual snake, starts
from a permitted initial history, or occurs on a path with the required global
length. Restricting to reachable states or incorporating endpoint information
may invalidate an obstruction and is a separate useful direction.

For the present proof plan, completing the missing share certificates remains
useful. An alternative route must change a substantive ingredient: remove
nonrealizable graph walks, use state-dependent boundary terms, or add geometric
constraints. Merely recomputing the potential on one of these relaxed graphs
cannot suffice.

## Reproduction

From the repository root, run `catalogue_test.py` by its repository-relative path
to regenerate the witnesses, then use the same path with `--verify`. The script
uses the local NumPy installation under `work/solver_packages`, the preserved
milestone72 graph, and the mixed-catalogue graph. The source model and every
array are hash checked before use. `data/verification.json` is the verification
receipt. The script makes no solver calls and supplies no new unconditional
upper bound.
