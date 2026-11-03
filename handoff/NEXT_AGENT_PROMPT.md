# Continuation after milestone 135

Use E:/Snake-in-a-box, the requested research skill, and ordinary notation.
Define only essential repeatedly used quantities. Preserve authors Iori Hironaka,
Tommy Ma and Steven Zhan and the existing hyperlink settings. Check GitHub each
round and preserve unrelated .gitignore and milestone 50 changes. Do not restart
an active proof job or repeat the large finite pair-capacity computation.

The previous round made progress: a complete actual-snake occurrence theorem
has passed Lean. Read milestone 135/MATHEMATICAL_NOTE.md, audit/statement-review.md,
the verification record and checkpoint. ActualCount135.low_pair_count_le_thirty_two
proves that any finite set of fitting canonical 012032 starts with pair sum <= 9
has size <= 32, regardless of length parity and allowing overlap.
ActualCount135.assigned_count_le_sixteen gives 16 for a fixed endpoint under the
unselected-common-neighbour assignment supplied by CommonNeighbor134. Do not
enlarge that premise to arbitrary Hamming-distance assignment without a bridge.

Checked building blocks now include:
- 132: low-pair windows force a qualifying endpoint, with complete certificate.
- 134: unselected common neighbour; one endpoint normalization for all windows;
  coordinate-pair representation; globally missing opposite pairs; injective
  actual coordinate lists; actual run-length bound using explicit finite sets.
- 135: even starts, separation of differently labelled windows, actual union
  capacity, injective reversal and halving, endpoint partition, and total 32.
- MissingDegree135: nonincident cardinal=t-degree; sum degrees>=t;
  sum(degree+crossing degree)=2t; with t=3 at most one A-vertex has three crossings.
  These are generic finite-edge theorems, to be instantiated with actual missing pairs.

NEXT SELECTED TASK: finish the stronger actual occurrence argument from
milestone 133/audit/occurrence-geometry.md. Construct maximal intervals from
sampled positions, prove their overlap count and unique exceptional prefix,
apply ActualRunBound134 with actual missing-pair sets, and derive their degree
and outside-coordinate cardinalities. Combine with OccurrenceArithmetic133.
For a<=7 the target inequalities are
W<=7a-a(a-1)/2-t-2k+delta and W<=k(5-a+t)-t+1+delta.
W>=12+delta forces a=k=5,t=3. The exceptional bound is W+3k<=6a-4+delta.
The final integer implications already passed. The new degree lemmas supply
their missing combinatorial sums, but the interval assembly is unfinished.
Handle a=8 separately using absence of missing pairs. Keep 12 per endpoint and 24
total labelled as pending stronger estimates; 22 also needs certified boundary
exclusion. The endpoint0 native UNSAT result from 133 is not a certificate.

The older two-endpoint 13 theorem has different hypotheses. The 133 witnesses
refute a uniform pair floor 10, including when both counts>=4. The fixed uniform
credit comparison in 132 cannot improve the numerical length bound with an
occurrence allowance>=2; further progress needs its remaining cycle constraint
or a stronger comparison. Do not claim total 32 alone lowers the global bound.

The next round is 136, when the full paper revision is due. Revise the open
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex in place and synchronize
the repo paper while preserving authors and hypersetup. Use mathematical prose,
not Lean identifiers, in the paper. Compile with the built-in tool and report
any infrastructure failure accurately. Current unchanged paper SHA256 is
4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90.

Recorded global interval 191–235 with incomplete independent contributor-upper
rebuild; optimum and 196 open; goal ACTIVE. Read saved process observations and
check the milestone 115 driver before any action involving that ongoing job.
