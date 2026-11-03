# Guarded six-count credit with the existing coefficient 24

The guarded variant preserves the old completed-profile mean and avoids the
loss caused by reducing all credits to coefficient 20. It still leaves the
integer comparisons unchanged. A six-count floor of 25 on $0123042$ yields
mean $2915/6$ in the completed-share profile and mean 496 in the conditional
profile, with their previous potential ranges.

## Why the existing last-five budget can be used

Use the manuscript's actual counts $\alpha_i$ and clipped counts $b_i$. If the
first of six symbols is below 6, then $\alpha_1=b_1$. A six-count floor gives

$$
\sum_{i=2}^{6}(\alpha_i-b_i)
\ge
\max\left\{0,L-\sum_{i=1}^{6}b_i\right\}.
$$

Thus the entire deficit belongs to the last five counts, which already carry
coefficient 24. The computation takes the maximum of the existing bonus and
24 times this guarded deficit. It does not add the two bonuses. The guard is
the first recorded count in chronological order; it is not reversed to move
the charge to a different five-position interval.

This is a conditional accounting argument. The independent Lean source checks
for its two statements in `GuardedCharge123` passed, as recorded in
`data/proof-review.json`. Application to the full graph and all local floor
premises remain separate verification obligations.

## Checked graph result

The $L=25$ run deletes 2,481 additional keys and increases the guarded credit
on 9,786 retained keys. It retains 4,680,633 edges. Keys containing symbol 6
are not deleted by treating that symbol as an exact count.

| Profile | Mean | Potential range | Comparison | Integer comparison |
| --- | ---: | ---: | ---: | ---: |
| Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |

The existing milestone-121 potentials are reused and checked on every retained
edge with the new weights. Each profile also has a retained cycle attaining
its stated mean. These two checks establish the exact finite-graph means;
the potential ranges are verified feasible ranges, without a new range
minimization.

The completed eighteen-cycle contains no matching $0123042$ window. The
conditional witness is the sum-24 three-cycle at edges 1130731, 2141975 and
15763, whose last-seven shapes are $0120310$ and $0123024$. It has no matching
$0123042$ window and no eligible endpoint event. Therefore both witness cycles
survive every larger floor with unchanged weights. The verified potential
inequalities remain valid by monotonicity.

The $L=26$ graph run was skipped after this obstruction was established, as
requested. Native evidence for floor 26 was separately pinned from the resumed
cap-25 probe; no graph result for an executed $L=26$ run is claimed. For all
larger floors, even allowing zero potential range leaves the limits

$$
\frac{1323416}{5623}>235,
\qquad
\frac{137866}{587}>234.
$$

Further strengthening only the $0123042$ sum floor cannot improve either
integer comparison in this family. The two sum-24 shapes recorded in the
uniform-20 report provide the next specific count-sum targets.

## Evidence and scope

Both original milestone-121 weight vectors and the complete removal set were
reproduced before the guarded modification. Every retained-edge potential
inequality passed. The saved-data audit rechecks source pins, cycle chaining,
maximum-credit weights, exact means, potential hashes/ranges and equality on
cycle edges, comparisons, and the absence of matching windows on the witnesses.
It is not an independent whole-graph reconstruction or a Lean proof.

Floors 25 and 26 have native negative evidence, with proof certificates and
semantic integration still separate. The inherited sum hypotheses and global
assembly are also unresolved. No actual-snake upper bound is established.
No SAT solver or Lean compiler was launched by this worker. The original
uniform-20 script and outputs remain unchanged.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_six_guarded.py` | `2ff7d3e0abcf931201ac2c696cffe18eefa4921e965030279a86f9026ea1171d` |
| `data/six-sum-guarded-graph/summary.json` | `9f612a67c073eb753fc880738c7e8cc5200a174700357feb2568625b74142ce4` |
| `data/six-sum-guarded-graph-l25/results.json` | `828b2de9ce666403493232f6e447435079a3fb01a2653b2a0aaed6626eebedaf` |
| `data/six-sum-guarded-graph/saved-cycle-audit.json` | `dd15c7936617d2682cec1b437de78ebf40ee9b4d6705383cb8b3efdb2ffd5fa7` |
