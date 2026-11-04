# Selected-row audit of the range obstruction

Status: `PASS_SELECTED_ROW_WALK_AND_CYCLE_AUDIT`.

The nine-edge walk has total weight 3,862 and deficit 602 at mean 496. All nine rows are retained by milestone 144. The fourteen-cycle is retained and has total weight 6,944. Neither witness contains a share-17 match or a uniform-credit occurrence event.

## Independent checks

The audit streamed the five required original archive columns, `U`, `V`, `weight`, `direction` and `count_code`, in blocks of at most 1 MiB. Each complete column hash matches `source-proved-model.json`. Only the 23 selected rows were retained in memory. The archive, metadata, direction model, removed-row list, count rules, execution result, preparation, plan and relevant scripts are hash-pinned in `walk-audit.json`. The native milestone-155 resource helper reported at least 1.5 GiB free memory before every column read.

For every selected row, the audit checked its original endpoints, direction index, chronological base-6 count decoding, milestone-144 retention and independently recomputed weight. The inherited count bonuses were recalculated from the count rules, pair rule and guarded six-count rule, preserving their maximum. All nine walk bonuses are zero. The adjacent eight-direction overlaps agree after renaming, adjacent five-count overlaps agree exactly, and the source and target vertices join. The same checks include the closing edge of the fourteen-cycle.

The chronological count word is

\[
(6,6,6,6,6,2,3,4,4,5,4,4,3,2).
\]

Each stored 6 denotes the interval \([6,21]\); it is not an exact count. The direction and count overlap checks establish a finite-graph walk. They do not establish an actual induced path in the cube.

| Source row | Suffix shape | Chronological suffix counts | Weight |
| ---: | :--- | :--- | ---: |
| 4001343 | 012310 | 6,6,6,6,2 | 252 |
| 4684655 | 012034 | 6,6,6,2,3 | 378 |
| 3607986 | 012304 | 6,6,2,3,4 | 496 |
| 1742134 | 012301 | 6,2,3,4,4 | 496 |
| 491026 | 012304 | 2,3,4,4,5 | 616 |
| 3069298 | 012304 | 3,4,4,5,4 | 496 |
| 987251 | 012301 | 4,4,5,4,4 | 496 |
| 1275893 | 012304 | 4,5,4,4,3 | 376 |
| 3049938 | 012304 | 5,4,4,3,2 | 256 |

## Comparison obstruction

Summing the potential inequalities along the walk gives

\[
R\ge 9\mu-3862.
\]

Summing around the fourteen-cycle gives \(14\mu\le6944\), hence \(\mu\le496\). Therefore, for \(\mu\ge0\) and zero uniform occurrence credit,

\[
\frac{1098960+8\mu+R}{4200+\mu}
\ge\frac{1095098+17\mu}{4200+\mu}
\ge235-\frac{30}{4696}.
\]

The derivative numerator of the middle expression is
\(17\cdot4200-1095098=-1023698<0\). At \(\mu=496\), the walk forces \(R\ge602\), and the recorded range-602 certificate attains the comparison \(551765/2348\). Feasibility of that certificate on all retained edges is the separately recorded main-run result; this audit did not repeat its all-edge scan.

The same obstruction extends to nonnegative uniform occurrence credit \(C\) on this fixed profile. The event is a 012032 suffix with both selected counts exact and their sum at most 9. Its count is zero on both witnesses. Their weight totals and the two inequalities above therefore remain unchanged. With the specified boundary cost \(24C\),

\[
\frac{1098960+8\mu+R+24C}{4200+\mu}
\ge\frac{1095098+17\mu+24C}{4200+\mu}
\ge235-\frac{30}{4696}.
\]

Thus the existing mean-496, range-602, zero-credit certificate attains the best comparison within this fixed finite profile, including varying nonnegative mean and nonnegative uniform occurrence credit, conditional on its recorded feasibility. This is stronger than a fixed-mean range statement. It supplies no arbitrary-snake bound.

## Local targets identified without a solver

Improving the 012032 share-17 condition alone cannot change either witness: neither contains that suffix shape. The nine-edge walk uses only 012310, 012034, 012304 and 012301 suffixes. A change capable of weakening this particular obstruction must raise a walk weight, delete a walk row with a justified exclusion, or change the graph/profile or comparison assumptions. Merely proving an already assumed floor leaves the numerical obstruction unchanged.

The following exact suffix patterns recur after canonical orientation, with reversal of the associated counts when required:

| Canonical directions | Exact canonical counts | Source rows | Current share floor |
| :--- | :--- | :--- | ---: |
| 012304 | 2,3,4,4,5 | 491026, 3049938 | 16 |
| 012304 | 4,5,4,4,3 | 3069298, 1275893 | 16 |
| 012301 | 4,4,5,4,4 | 987251 | 16 |

The first two pairs are therefore natural prospective local targets. For example, a valid share floor 17 on either exact 012304 pattern would increase the two corresponding witness weights by one each. A valid exclusion for either pattern would remove those two witness rows. Such changes would weaken or remove this witness; they would not by themselves establish an improved optimum because other walks may obstruct it. No feasibility test, exclusion, new share floor or actual-snake realization is claimed here.

## Scope limits

No optimizer, solver, full graph reconstruction, all-edge inequality scan, Lean compilation, TeX compilation or Git operation was run. The archive's unused history column was not loaded. The main-run counts of 156 source matches, 91 retained matches and 77 increased retained rows were not independently recounted. The selected-row audit establishes that none of those increases affects the nine-edge walk or fourteen-cycle.

All inherited conditional floors, count rules, six-count assumption, reference obligations and graph-to-snake interpretation obligations remain. The audit verifies the selected finite-graph obstruction and its arithmetic, with the separate recorded feasible certificate supplying attainment.
