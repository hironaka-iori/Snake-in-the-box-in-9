# Six-count restrictions and their remaining obstructions

## Result

The recovered six-fours exclusion and the tested six-count sum restrictions do
not improve the integer comparisons. The maintained interval remains
$191\le a(9)\le235$, with the previously recorded limitation on the independent
rebuild of 235. The comparison 234 still has unproved premises. This round does
not establish the optimum or the conjectured value 196.

The new candidate is

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge26
$$

for a fitting seven-transition window with canonical directions $0123042$.
The counts and the notation $b_i=\min\{6,\alpha_i\}$ and
$\delta_i=\alpha_i-b_i$ are those already used in the manuscript. No new
mathematical definition is introduced. The proposed inequality is unproved.

## Why the original exclusion is insufficient

Saved milestone 32 case 10 excludes the exact count tuple$(4,4,4,4,4,4)$ on
$0123042$. Its original formula, renaming and saved certificate were recovered.
The backward-trimmed certificate has 55,823 deductions and 3,570,165 hints.
The exporter checks its propagation steps, and the independent archive audit
checks its exact provenance and dependency closure. Two hundred and two Lean
modules have been generated. The concrete formula and its satisfiability
interpretation have been checked; the contradiction replay remains pending.
No actual-snake exclusion is newly claimed from that partial work.

Granting case 10 removes 13 additional graph keys. Granting every one of the 34
saved six-fours exclusions removes 155 retained six-fours keys. Even combining
that stronger hypothetical deletion with deletion of all 9,577 endpoint-eligible
keys preserves the means$2915/6$ and$496$, hence the integer comparisons 235
and 234. The surviving six-cycle has rotations of$(4,6,2,2,6,4)$. Every symbol 6
still represents the full interval$[6,21]$.

This observation motivated a sum restriction that applies when some actual
counts exceed the clipping threshold.

## Evidence for the sum restriction

All 134 saved paths were checked for distinctness and induced adjacency,
using 2,432,200 pair checks. Among 1,298 occurrences of$0123042$, the smallest
six-count sum was 43. Across all seven-direction shapes in these saved paths,
the smallest sum was 31. These are observations on a finite bank of paths;
neither is a universal lower bound.

Full-cube counterexample tests use all 512 vertices and all six count bounds
$[0,21]$. The six corner lists contain 126 literal occurrences across 106 distinct
vertices. Multiplicities are retained:20 vertices contribute twice. The
independent reconstruction agrees with the encoded counters.

| Counterexample condition | Outcome | Solver time | Saved cycle cuts |
|---|---|---:|---:|
| Six-count sum at most24 | Uncertified contradiction |13.766s|4|
| Six-count sum at most25, first attempt | Unresolved |30.062s|13|
| Six-count sum at most25, resumed | Uncertified contradiction |34.313s|19|

Each saved cut excludes a finite selected subgraph with minimum internal degree
at least two. Such a graph contains a cycle and cannot occur inside an induced
path. All cuts have been independently checked. The final reconstructed
clause totals are 101,902, 102,162 and 102,168. The raw probe field counts clauses
before newly found cuts are sent to the solver; it must not be treated as the
final formula size.

The saved census tuples describe the last discarded cyclic models. No selected
path was returned. A contradiction certificate, its count-sum semantics and its
transfer to arbitrary snakes are still required to prove the candidate 26.

## Counting overlapping windows

For any nonnegative sequence$\delta_i$, a position occurs in at most six
consecutive six-centre windows. Therefore

$$
\sum_{r=0}^{N-1}\sum_{j=0}^{5}\delta_{r+j}
\le6\sum_{i=0}^{N+4}\delta_i.
$$

For$N=0$, the left side is empty and the inequality still holds. Thus a credit
bounded by$20\sum_{j=0}^{5}\delta_{r+j}$ in each window uses at most
$120\sum_i\delta_i$ overall. If the local sum is at least$L$, its clipped deficit
satisfies

$$
\max\left\{0,L-\sum_{j=0}^{5}b_{r+j}\right\}
\le\sum_{j=0}^{5}\delta_{r+j}.
$$

To use this six-centre coefficient 20 together with an existing five-centre
credit, the old coefficient 24 is first reduced to20. The two credits are
combined by their maximum. Adding them would count the same excess twice.

There is a useful special case. If$b_r<6$, then$\alpha_r=b_r$ and$\delta_r=0$.
The entire six-count deficit then belongs to the last five positions:

$$
24\max\left\{0,L-\sum_{j=0}^{5}b_{r+j}\right\}
\le24\sum_{j=1}^{5}\delta_{r+j}.
$$

The existing five-centre coefficient 24 can consequently be retained on these
windows, again combining credits by their maximum. Lean checked
these counting deductions under their explicit local premises. They do not
prove the proposed lower bound$L$.

## Graph tests and next useful target

The coefficient 20 experiments at$L=25,26,27$ preserve the conditional mean 496.
The other mean decreases to$2428/5$ because its old coefficient was reduced.
The integer comparisons remain235 and 234. An attaining cycle at$L=25$ contains
no$0123042$ window, so increasing$L$ cannot change that cycle's weights or
remove it. The final graph reviews also evaluate the coefficient 24 special
case and give the exact zero-range comparisons.

The conditional three-cycle from the coefficient 20 experiment has keys
1130731,2141975 and15763, direction words$012302432$, $012314210$ and
$012031043$, and six-count tuples rotating$(3,5,4,3,5,4)$. This is a cycle of
the finite model; no realization by a snake is asserted.

Further effort on$0123042$ alone cannot eliminate this obstruction. The next
focused check should test whether the six-count sum is at least 25 for
$0120310$ or $0123024$ (whose reverse is $0123142$), preserving all count
intervals and inherited proof premises. Either restriction would remove
a displayed exact tuple; an improved graph comparison would still need testing. A broader
six-count hypothesis is a possible question for the next round, not a theorem
or a new bound established here.

## Saved evidence and continuation

- `audit/case10-review.md`: original case, archives, renaming and reduced proof.
- `audit/six-graph-review.md`: exact-six-fours and endpoint experiments.
- `audit/six-sum-probe-review.md`: full-cube counters, cut validity and outcomes.
- `audit/six-sum-graph-review.md`: coefficient 20 experiments and surviving cycles.
- `audit/six-sum-guarded-review.md`: coefficient 24 experiment and its limitations.
- `audit/proof-review.md`: exact checked Lean statements and dependency reports.
- `data/batch-observation.json`: process-backed snapshots of the older 104, 115
  and 122 proof batches. Their partial progress remains separate from a proof.
- `data/file-manifest.json`: immutable local checkpoint, including all generated
  case 10 sources. No case 10 contradiction batch was launched in this round.

Paper revision 116 remains unchanged; the next full manuscript revision is 126.
The three authors and local hyperlink settings remain unchanged.

The final proof review covers five modules and seven printed dependency
reports. They contain only the standard foundations listed in the receipts.
The inherited receipt scope sentence mentioning an actual-snake exclusion is
inaccurate for these modules; the reviewed statements concern conditional
CNF semantics and counting arithmetic only.
