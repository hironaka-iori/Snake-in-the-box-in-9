# Six-count case 10 and endpoint-credit comparisons

Case 10 removes 13 additional graph keys and breaks the previous all-four
three-cycle. It does not improve either numerical comparison. Combining it
with the endpoint credit, or even deleting all endpoint-eligible suffixes,
also leaves both minimum means unchanged. A stronger diagnostic granting all
34 six-count exclusions has the same outcome.

## Exact case and experiments

Saved case 10 has seven directions $0123042$ and six internal counts equal to 4.
The graph test uses the last seven directions of a nine-transition key and
all six recorded count symbols. The canonical reverse of $0123042$ is again
$0123042$; the count tuple is symmetric. The source case table and saved
certificate metadata agree on both directions and intervals.

All 13 source-graph matches are retained by the milestone-121 model. Their
deletion removes edge 3049577 of the milestone-122 three-cycle. The completed
profile's eighteen-cycle survives. The inherited thirteen sum rules, pair
restrictions, weight vectors and coefficient budget are unchanged.

| Experiment | Profile | Mean | Potential range | Corrected comparison | Integer comparison |
| --- | --- | ---: | ---: | ---: | ---: |
| Case 10 alone | Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Case 10 alone | Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |
| Case 10 and endpoint credit $C=4$, budget 13 | Completed-share | $2915/6$ | $1730/3$ | $6620852/28115$ | 235 |
| Case 10 and endpoint credit $C=4$, budget 13 | Conditional-share | $496$ | $602$ | $551791/2348$ | 235 |
| Case 10 and all endpoint-eligible suffixes deleted | Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Case 10 and all endpoint-eligible suffixes deleted | Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |
| All six-fours keys and all endpoint-eligible suffixes deleted | Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| All six-fours keys and all endpoint-eligible suffixes deleted | Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |

The finite-credit comparison includes its full conditional occurrence cost:

$$
m\le\frac{1098960d+13Cd+8p+R}{4200d+p}.
$$

The scheduled coefficients were $4,16,32,64$. At $C=4$, the attaining
conditional cycle contained no eligible suffix. The larger coefficients were
therefore skipped. They cannot increase the mean while that cycle survives.
No numerical results are claimed for unexecuted coefficient runs.

The ideal deletion removes all 9,577 eligible endpoint suffixes. It is a
stronger hypothetical restriction than the occurrence allowance $t\le13$.
The final diagnostic additionally removes all 155 retained keys with six
counts equal to 4. Each of those 155 keys was matched, up to coordinate
renaming and reversal, to one of the 34 saved seven-direction cases. This
diagnostic therefore grants the entire six-count exclusion premise; it does
not establish that premise.

## Surviving obstruction

Case 10 alone retains the milestone-121 conditional four-cycle. After ideal
endpoint deletion, a six-cycle remains:

| Edge | Nine directions | Six count symbols | Weight |
| ---: | --- | --- | ---: |
| 3050240 | $012341254$ | $(4,6,2,2,6,4)$ | 496 |
| 991818 | $012301430$ | $(6,2,2,6,4,4)$ | 496 |
| 1272514 | $012304235$ | $(2,2,6,4,4,6)$ | 736 |
| 3047869 | $012341254$ | $(2,6,4,4,6,2)$ | 256 |
| 992784 | $012301430$ | $(6,4,4,6,2,2)$ | 256 |
| 1275960 | $012304235$ | $(4,4,6,2,2,6)$ | 736 |

Every history value, inherited additional bonus and endpoint credit is zero.
The weight sum is 2,976, giving mean 496. This same cycle survives deletion of
all six-fours keys. The symbol 6 retains its full interval $[6,21]$; these are
graph count contexts, with no actual-snake realization established here.

The distinct canonical five-count contexts are

$$
012304:\quad(4,6,2,2,6),\ (2,6,4,4,6),
$$

$$
012301:\quad(2,2,6,4,4),\ (4,4,6,2,2).
$$

The zero-eligible six-cycle bounds the conditional mean by 496 for every
nonnegative endpoint coefficient. The earlier lower potential inequalities
remain valid after nonnegative credits, so the minimum mean stays exactly
496. Even granting zero occurrence cost and zero potential range gives
$137866/587>234$. The corresponding completed-profile value is
$1323416/5623>235$.

Thus case 10, or even all 34 six-count exclusions combined with this endpoint
event, cannot improve the current integer comparisons within this graph family.
Completing their certificates may reduce proof obligations, but it has no
demonstrated numerical benefit here. The next numerical target should affect
the displayed six-cycle, for example a restriction or coupled count bound on
one of its $012304$ contexts. Any test must preserve the full $[6,21]$ intervals.

## Verification and limitations

The producer reconstructs the milestone-121 removal set and reproduces both
full retained weight-vector hashes before adding case 10. Every retained edge
was checked against each of the eight reported potentials, and every reported
mean has an attaining saved cycle. No coefficient optimization was repeated
after the zero-eligible cycle was found.

The second saved-data check verifies source pins, cycle chaining, exact means,
the weight/credit relation, decompressed potential hashes and ranges, equality
on cycle edges, corrected comparison arithmetic and coverage of all 155
six-fours keys by the saved case list. This is a producer computation and
saved-data audit, without an independent reconstruction of all edge inequalities
or a Lean proof. No SAT solver or Lean compiler was launched by this worker.

The case-10 theorem, endpoint occurrence bound and inherited sum hypotheses
retain their separate proof obligations. The ideal deletion and all-34-case
diagnostic have stronger premises than the finite-credit experiment. No global
actual-snake bound is established by these calculations.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_six.py` | `f92248eb961e9cc7407cf9eae57dace56ce7a7d8e79b9f09ff56d13a91dfec1f` |
| `data/six-graph/summary.json` | `7ad050f854365d2d689638555b47e3e6a70d1521ce080437db428321245688b2` |
| `data/six-graph/saved-cycle-audit.json` | `95a13d446590f8bd6daf522a0953d4825c9e0f770aaf7a8a1a2902e542fa2231` |

Only the assigned milestone-123 graph files were written. Earlier milestones,
proof sources and checkers, active jobs and root documents were left unchanged.
