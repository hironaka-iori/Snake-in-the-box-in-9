# Milestone 124: six-count coverage and direct length criteria

Read [the mathematical note](MATHEMATICAL_NOTE.md). Lean proves that six
internal counts sum to at least 25 for direction pattern 0123041, in either
orientation, in an actual snake. This closes one of 21 reversal classes.

Lean also checks bounds 234 and 233 under the respective universal six-count
floors 25 and 26. A weaker sufficient condition for 234 allows total shortfall
at most 28 across 39 disjoint groups of six counts. These additional assumptions
remain unproved. No new mathematical definition is needed.

The full-cube screen has negative results on 19 classes, including the checked
class; 0120310 and 0120324 remain unresolved. The other 18 negative results still
need checked proofs. The independent [proof review](audit/proof-review.md),
[coverage review](audit/coverage-review.md) and [probe review](audit/probe-review.md)
separate these evidence levels.

The [graph review](audit/graph-review.md) shows why increasing the three original
pattern floors cannot improve the tested integer comparisons. The maintained
range remains 191–235 with its documented independent-rebuild limitation. The
optimum and 196 remain unresolved. Paper revision 116 is unchanged; the next
full revision is 126.
