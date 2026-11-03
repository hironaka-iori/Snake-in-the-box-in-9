# Six-count sum sensitivity with coefficient 20

Increasing the proposed six-count floor for direction pattern $0123042$ does
not improve either integer comparison in this graph family. The checked
experiments at $L=25,26,27$ have the same means and ranges. Their surviving
cycles avoid that direction pattern, which gives an obstruction for every
larger floor without further graph runs.

## Shared charge and finite results

The computation reproduces the milestone-121 removal set and both original
weight vectors. Every old extra bonus is verified divisible by 24. The old
bonus is then replaced by 20 times its previous deficit. For a matching final
seven-direction window, the new credit is

$$
20\max\left\{0,L-\sum_{i=1}^{6}b_i\right\}.
$$

The new extra bonus is the maximum of these two credits. They are never added
together. This uses coefficient 20 at each of six count positions, with total
120. The independent Lean source checks for the generic overlap and shared-credit
accounting in `SixCharge123` passed, as recorded in `data/proof-review.json`.
Application to the full graph and the local count-sum premises remain separate.

A matching key is deleted only when all six symbols are below 6 and their sum
is less than $L$. Symbol 6 retains its full interval $[6,21]$; it can produce
excess credit but is never silently replaced by an exact count 6.

| Floor | Additional deletions | Keys with increased six-count credit | Completed-share comparison | Conditional-share comparison |
| ---: | ---: | ---: | ---: | ---: |
| 25 | 2,481 | 9,966 | $5517087/23428$, integer 235 | $551765/2348$, integer 234 |
| 26 | 4,609 | 20,782 | $5517087/23428$, integer 235 | $551765/2348$, integer 234 |
| 27 | 6,212 | 35,439 | $5517087/23428$, integer 235 | $551765/2348$, integer 234 |

The completed-share mean is $2428/5$ and its potential range is $2863/5$ in
each run. The conditional-share mean is 496 and its potential range is 602.
Reducing the old coefficient from 24 to 20 lowers the completed-profile mean
slightly below its former $2915/6$. The guarded variant in the separate report
avoids this loss, without improving the integer comparisons.

At the start of this sweep, floor 25 had an uncertified native negative probe;
the initial floor-26 probe was UNKNOWN, and floors 27 and 28 were hypothetical.
A later resumed probe supplied native negative evidence for floor 26. The
original sweep's input records retain their earlier status and exact bytes.
None of these statuses alone is a checked local theorem or global bound.

## Obstruction for every larger floor

The $L=25$ completed ten-cycle contains no $0123042$ window and no eligible
endpoint event. The conditional three-cycle has the same two properties:

| Edge | Nine directions | Six count symbols | Canonical last-seven shape | Six-count sum |
| ---: | --- | --- | --- | ---: |
| 1130731 | $012302432$ | $(3,5,4,3,5,4)$ | $0120310$ | 24 |
| 2141975 | $012314210$ | $(5,4,3,5,4,3)$ | $0123024$ | 24 |
| 15763 | $012031043$ | $(4,3,5,4,3,5)$ | $0123024$ after reversal | 24 |

For the last row, forward canonicalization gives $0123142$; reversal gives
$0123024$ and reverses the counts to $(5,3,4,5,3,4)$. The other rows use their
forward count order. These are graph contexts, without an actual-snake
realization established by this computation.

For every $L\ge25$, increasing $L$ can only increase weights or delete matching
keys. The two displayed witness cycles remain unchanged because they contain
no matching window. The $L=25$ potentials therefore remain valid, and the
unchanged cycles give the opposite inequality. The means are fixed at
$2428/5$ and 496 for every larger floor in this model. The conditional cycle
also avoids the endpoint credit, so adding such credit cannot increase its mean.

Even granting potential range zero gives

$$
\frac{1378556}{5857}>235,
\qquad
\frac{137866}{587}>234.
$$

Consequently no larger floor on $0123042$, smaller potential range, or
nonnegative credit on the current endpoint event can improve these integer
comparisons while the cycles remain. The $L=27$ run returned another attaining
conditional cycle with an eligible endpoint event, but the $L=25$ zero-event
cycle still survives and supplies the stated obstruction.

The next focused count-sum targets are $0120310$ and $0123024$. A floor of 25
on either matching exact sum-24 context would remove the corresponding edge.
`data/six-sum-graph/next-targets.json` saves the complete orientation records and
two proposed full-Q9 cap-24 inputs. They are explicitly untested; no new probe
was launched by this worker.

## Controlled stop and verification

The requested optimization arrived while $L=27$ was already running. That run
finished successfully. The still-unstarted $L=28$ output directory was reserved
with an explicit skipped record; the producer's existing overwrite guard then
stopped the driver before computing $L=28$. No active source or earlier output
was changed. The original summary retains its intermediate RUNNING label;
`data/six-sum-graph/execution-stop.json` records the terminal driver result and
supersedes that process status. This intentional boundary stop is unrelated to
any mathematical check or compiler failure.

Every retained-edge potential inequality was checked for the six completed
profile/floor combinations, and attaining cycles are saved. The subsequent
saved-data audit verifies source pins, cycle chaining, exact means, coefficient
rescaling, maximum-credit composition, potential hashes/ranges and tightness,
comparison arithmetic, and the zero-match witness properties. It does not
independently reconstruct the whole graph or provide a Lean proof.

All local floors, inherited sum rules, application of the checked accounting to
the full graph, and global assembly retain their separate proof obligations.
No actual-snake upper bound follows from this sensitivity experiment. No SAT
solver or Lean compiler was launched by this worker.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_six_sum.py` | `38730604a21a207705ce05be565d8137dd9d800cbd5e8bdd625c686ba73362aa` |
| `data/six-sum-graph/execution-stop.json` | `fcf9fa4d587dd8eca13080e27bf4eda3ff5ea050d8fb2ab08360578915991e9a` |
| `data/six-sum-graph/saved-cycle-audit.json` | `dda45d4cc031c03ec039c44bf20d3ca28b705bdd1d2a530ec66f358880a12fe3` |
| `data/six-sum-graph/next-targets.json` | `2ac5f5b2bb2fc283af5d7cb543576dcc66cba688f4b05e1313c1710527d63399` |
