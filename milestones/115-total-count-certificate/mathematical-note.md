# Five-count inequalities and their current limits

This round retains the existing singleton-square counts and introduces
no mathematical definitions.

## The proof already being checked

For canonical direction pattern `012310`, the target is

\[
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}
+\alpha_{r+4}+\alpha_{r+5}\ge19.
\]

The previous native contradiction has been reduced to 287,753 deductions
and 16,816,989 propagation hints. Every deduction passed an independent
RUP checker after its input references were mapped to the original
formula. Four bounded refinement attempts were retained; the smallest
selected proof was not the last attempt.

Lean checks that an actual local configuration with total at most 18
would satisfy the selected clauses. This includes all 105 occurrences
in the sum counter, representing 84 distinct vertices, and the selected
induced-cycle exclusion. Repeated occurrences are necessary because the
same vertex can contribute to several counts. The concrete semantic
module's two theorem audits use only the standard three logical axioms.

The complete refutation export passes native simulation. Its first
contradiction group also passed Lean. The remaining groups and final
composition are being checked sequentially. Until those checks finish,
the actual-snake inequality is not recorded as a completed Lean theorem.

## Six distinct directions

The next candidate has a simpler statement:

\[
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}
+\alpha_{r+4}+\alpha_{r+5}\ge23
\]

whenever the six consecutive transition directions are distinct. The
canonical representative is `012345`.

The initial test imposed a middle count at most 3 and rejected total at
most 21. Subsequent tests removed the middle-count condition. Totals at
most 20 and 21 were rejected without additional cycle cuts. A 20-second
test of total at most 22 was inconclusive; a separate longer test rejected
it in 28.391 seconds after five added induced-cycle exclusions. Each
exclusion was independently checked for containment, connectedness and
induced degree two. The sum has 105 occurrences and 89 distinct vertices.

The solver also produced a local forest with counts

\[
(6,3,6,2,6),\qquad 6+3+6+2+6=23.
\]

Independent inspection verifies its window, degrees, endpoint budget,
acyclicity and exact counts. Its component sizes are
\(43,27,24,9,1,1\). It therefore provides local feasibility at total 23;
it does not construct a single snake. Together, the solver results and
this witness suggest a sharp lower bound of 23 in the radius-four local
model. The negative result still needs an independently checked
contradiction certificate, followed by its Lean interpretation and replay.
Sharpness for complete snakes is unresolved.

Additional controls show why some tempting simplifications fail in the
local model. Both end counts can equal 3. They can still equal 3 when the
middle count is 4, as witnessed by \((3,15,4,14,3)\). Thus the end caps
alone, or end caps together with that middle cap, are not local
contradictions. Five positive local witnesses were independently checked.

## Effect on the graph comparisons

All experiments retain the previous shared charge budget. Competing
credits are combined by their maximum. No additional copy of the budget
is assigned to a new inequality.

| Added assumptions on `012345` | Completed-floor mean | Potential range | Conditional mean and range |
| --- | --- | --- | --- |
| Middle count at most 3 implies total at least 22 | \(3396/7\) | \(4089/7\) | 496 and 602 |
| The preceding rule and universal total at least 21 | \(6309/13\) | \(7656/13\) | 496 and 602 |
| Universal total at least 22 | \(6309/13\) | \(7656/13\) | 496 and 602 |

Each experiment checks a potential inequality on every retained edge
and saves an attaining cycle. Independent reviews check the saved cycles,
full graph keys, weights, potential hashes and ranges, and exact comparison
arithmetic. They do not repeat the full-edge scans.

The final completed-floor comparison is

\[
m\le\frac{4781536}{20303},
\]

under all the required local and graph assumptions. Its integer part is
235. The conditional-floor comparison remains \(551765/2348\), with
integer part 234. The completed-floor designation describes the source of
the share floors; the newly added count inequalities remain assumptions
in these experiments.

The existing comparison excludes length 235 only if

\[
227p>111960d+R,
\]

where \(p/d\) is the finite mean and \(R\) is the nonnegative range of
the scaled potential. The value \(6309/13\) is below
\(111960/227\), so even a zero range cannot improve this comparison to
234. Likewise, the conditional mean 496 is below the threshold needed
to exclude 234. Range optimization alone cannot change either integer.

The attaining cycles saved for universal total at least 22 contain no
`012345` window at either eligible placement. Strengthening that rule to
23 therefore leaves those cycles unchanged. It only removes other edges
or increases their credits, so the previous potential inequalities remain
valid. Consequently, the same means and the same valid potential ranges
remain available under the stronger candidate. No new full-edge scan is
needed for this monotonicity conclusion. A smaller range might exist,
but it cannot overcome the preceding arithmetic thresholds.

This identifies a useful stopping point for this family: stronger
`012345` count inequalities alone cannot improve the present comparisons.
Progress toward a smaller upper bound must affect the remaining cycles
through a different valid restriction or a justified change in the global
accounting.

## Status

The maintained global interval is 191 through 235 edges, based on the
contributor proof and archived audit, with a complete independent rebuild
pending. No new global upper bound or exact optimum is established here.
The `012310` Lean batch continues, and the `012345` lower bound of 23 is
a precisely stated candidate with positive local control evidence and a
pending negative certificate. Paper revision 106 is unchanged.
