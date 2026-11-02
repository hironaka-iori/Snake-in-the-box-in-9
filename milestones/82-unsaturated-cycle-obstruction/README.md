# Milestone 82: obstruction from a cycle with counts below six

Adding charge only when some stored count equals six cannot improve the
minimum cycle mean of the current graph. A four-edge attaining cycle has
all six stored counts strictly below six on every edge. Every nonnegative
bonus that vanishes on such edges leaves the exact mean at 483.

Under the current global budget, this also prevents an upper bound of 234
through any constant slope and nonnegative potential range on that augmented
graph. This is a result about the finite comparison graph. Realization of
the cycle by an actual snake remains unresolved. The project interval remains
191 through 235 edges, with the same contributor-evidence qualification.

## Exact witness and argument

The source graph has 1,601,856 states and 4,947,008 edges. Reconstructing the
weights from the completed local shares reproduces their recorded hash.
Every edge inequality for the recorded potential was checked again, giving
minimum mean 483 and potential range 551. The following cycle attains it:

| Edge index | Source | Target | Weight | Six stored counts |
| ---: | ---: | ---: | ---: | --- |
| 372796 | 114400 | 593089 | 252 | 5, 2, 4, 5, 5, 2 |
| 2610423 | 593089 | 1147977 | 480 | 2, 4, 5, 5, 2, 4 |
| 3534483 | 1147977 | 394906 | 600 | 4, 5, 5, 2, 4, 5 |
| 1650991 | 394906 | 114400 | 600 | 5, 5, 2, 4, 5, 5 |

Its total weight is 1932, so its mean is 483. Let a new edge weight be
\(w'(e)=w(e)+B(e)\), where \(B(e)\ge0\), and suppose \(B(e)=0\)
whenever all six stored symbols are below six. The existing potential remains
valid because every edge weight is nondecreasing. The displayed cycle keeps
weight 1932. Hence the new minimum cycle mean is exactly 483.

For a rational potential with slope \(p/d\), where \(d>0\), summing its four
edge inequalities gives \(p\le483d\). A nonnegative scaled potential range
\(R\) therefore satisfies

\[
227p-R\le109641d<111960d.
\]

The current budget excludes a 235-edge path only if
\(227p-R>111960d\). Thus no potential satisfying this fixed graph and budget
can establish that exclusion. Even the idealized range zero yields only

\[
\frac{1098960+8\cdot483}{4200+483}
=\frac{367608}{1561}>235.
\]

The missing amount in the strict criterion is already 2319 at range zero
and scale one. Improving the potential range alone cannot resolve it.

## Consequence for the next charge targets

The idea tested here was to recover excess above the truncated count of six,
using the existing triple-sum theorem from milestone 50. That theorem and the
mixed demand accounting in milestone 51 are prior project work. This round
does not claim a new local inequality or a new method for excess accounting.

The displayed cycle instead identifies two pending share targets that act on
its edges: case 7302, shape 012034 with floor 20, and case 7307, shape 012340
with floor 16. On this witness, 012034 appears twice and 012340 once. Applying
both proposed floors would raise its total by 56 and its mean to 497.

This last calculation is conditional and concerns this one witness only.
The two floors remain unproved. Other cycles can determine a lower complete-
graph mean, and the other three pending target cases remain obligations of
the full proposed 234 certificate. The useful next test is a certificate or
counterexample search for these two local targets, rather than another
threshold-six bonus on the unchanged graph.

## Verification and limitations

Six Lean theorem audits passed. They check the literal count list, weight
sum, telescoping cycle argument, rational budget obstruction and monotonicity
of the potential inequality under a nonnegative bonus. The audits contain
only standard axioms or no axioms. The finite array correspondence and all
4,947,008 edge inequalities were checked separately in Python. The entire
graph is not replayed in Lean by this milestone.

The inherited mathlib environment was reused. The arithmetic proof has no
dependency on the local snake-certificate caches. The existing completed
local-share receipts are checked by hash when reconstructing the graph.
No new global upper bound, construction or optimality result follows.

The obstruction assumes the current graph remains intact and the same global
budget is used. Removing edges using geometric information, strengthening
shares on edges with exact counts below six, or changing the boundary budget
can evade it. Bonuses depending on unavailable counts or longer windows are
outside the stated six-symbol support condition.

## Files and reproduction

Run these scripts from the repository with the recorded Python runtime:

1. `scripts/check_graph.py`: exact array hashes, weight reconstruction,
   potential inequalities and attaining cycle; writes the literal Lean input.
2. `scripts/check_lean.py`: six Lean checks and source/object/log audit.
3. `scripts/target_cycle.py`: conditional sensitivity of this witness only.
4. `scripts/finalize.py`: combine receipts and current repository checkpoint.
5. `scripts/verify_saved.py --verify`: check the frozen local file manifest.

See [data/graph-audit.json](data/graph-audit.json),
[data/lean-audit.json](data/lean-audit.json),
[data/target-sensitivity.json](data/target-sensitivity.json), and
[audit/review.md](audit/review.md). Sources, logs and exact hashes are saved;
compiled caches remain local. Runtime paths require adaptation on another
host. Re-running the checks changes timing receipts and requires a new
checkpoint and manifest.

The paper remains revision 76, with the existing editor source and repository
mirror unchanged. The next scheduled full revision is 86. No new PDF result
is claimed.
