# Next potential test after the local share-17 theorem

Use milestone 144's retained graph, the full conditional share profile, and
zero uniform occurrence credit. Optimize the potential range at mean 496.
This is one finite-graph experiment on the empty-square route. No new snake
bound or completed potential is asserted here.

## Exact graph, profile and weight

Keep all 1,601,856 original states and exactly the 4,661,572 rows retained by
144/data/share18-impact/removed-indices.json from the 4,947,008-row source
graph. Make no new exclusions. In shape order 012031, 012032, 012034, 012301,
012304, 012310, 012314, 012340, 012345, use floors

\[
(16,16,18,16,16,12,16,16,16).
\]

The four unfinished floors remain 012034:18, 012301:16, 012340:16 and
012345:16. Universal 012032 share16 is already checked. Start only after
the final actual-snake share17 audit passes with its count hypotheses.

Decode the six chronological count symbols. Match only the six-direction
suffix, directions[3:9], and its five internal counts, counts[1:6], using
zero-based half-open indexing. Match canonical 012032 with counts
(4, at most 4, 4, at most 5, 3), or canonical 012032 after reversing both
sequences. Combine the orientations by logical OR. Stored 6 represents
[6,21] and cannot match these intervals. The earlier prefix earns no credit.

Use the edge weight

\[
\max\{w_{\mathrm{source}},\,120b_{\mathrm{last}}+
       \max(F_{\mathrm{shape}},17\mathbf1_{\mathrm{match}})\}
 +\max\{B_{\mathrm{old}},B_{\mathrm{pair}},B_{\mathrm{six}}\}.
\]

The last maximum is exactly the existing shared count bonus reconstructed
by milestone 144. Preserve its guards and assumptions. Replace the share
floor by 17 where applicable; do not add 17 to 16, or award prefix and suffix
credits to the same occurrence. Use uniform credit C=0, with no 24C boundary
cost. The saved inventory gives 91 matching retained suffix rows and 156
source suffix rows. The number of rows whose weight increases must still be
checked, because an existing maximum may dominate the new floor.

## Assumptions retained

The 144 producer inherits interval/sum exclusions and bonuses supported by
records marked UNSAT_UNCERTIFIED, the hypothetical six-count floor 25 on
0123104, and pair floor 9 for odd-length snakes. The six-count bonus keeps
the first chronological stored symbol below 6 as its guard; the associated
exclusion requires six exact counts with sum below 25. The three count
bonuses share a budget and are combined by a maximum. Checked exclusions
from milestones 138 and 140 do not discharge all preceding hypotheses.
The JSON retains the count rules and all 73 predecessor input hashes.

The conditional 234 argument also retains its reference and potential
obligations: 1,358 unresolved entries of the 1,378-key reference union and
the complete 791-context certificate and assembly. A numerical scan does
not discharge those Lean obligations or the extra 144 graph interpretation.
Pair 9 applies to odd edge lengths including 235; longer induced paths have
235-edge prefixes. This observation leaves the other premises unchanged.
The maintained 191--235 interval keeps the contributor-proof and incomplete
independent-rebuild distinction.

## The original source graph already has a fixed limitation

The original graph avoids the later count/six-floor assumptions. However,
reweighting its saved rows under universal 012032 share16 and the new
count-conditioned share17 leaves the three-cycle total at 1,488 and the
28-edge walk total at 13,286. Neither has a share17 match. Therefore

\[
\mu\le496,\qquad R\ge28\mu-13286.
\]

For nonnegative mean and range and C=0,

\[
\frac{1098960+8\mu+R}{4200+\mu}
\ge\frac{1085674+36\mu}{4200+\mu}
\ge235-\frac{30}{4696}.
\]

The last rational function decreases with the mean. The saved all-edge
potential attains mean 496 and range 602; it remains valid when the share17
weights increase. These saved records thus determine the best comparison
for this particular original finite profile. A new all-edge optimization
of that profile would be redundant. This task recalculated saved rows and
hashed the old certificate; it did not reload graph arrays or repeat the
previous all-edge check. This finite-profile conclusion is not a snake bound.

Two three-cycle edges and three edges of the 28-edge walk are removed in
graph 144. Their inequalities must not be transferred to the retained graph.

## The surviving cycle sets the next test

The eleven-cycle increases from 5,456 to 5,458, with two share17 matches.
The fourteen-cycle has no 012032 suffix and receives no share17 credit.
Adding only 012032 share16/17 to the old 144 profile leaves its total at
6,890, caps the mean at 3445/7, and forces comparison at least
235+341/6569. That profile cannot reach 234.

Under the selected full conditional vector, 012301 share16 adds 30 and
012340 share16 adds 24 to the fourteen-cycle. Its weights become

\[
256,256,736,496,376,736,376,496,496,376,736,376,496,736.
\]

Their sum is 6,944, so the retained restriction is mu at most 496. Its
first two edges, 973890 and 1205785, have weight 512, giving

\[
R\ge2\cdot496-512=480
\]

at the target mean. The saved source potential supplies feasibility and
range at most 602 because weights only increase and rows are removed.
The useful fixed-mean range interval is therefore [480,602]. Seek R<602.

## Reproducible execution specification

The next script to implement is work/after155_potential_test.py. It has not
been written or run. The accompanying JSON pins the reconstruction inputs,
saved row recalculations, weights, recognition rules and execution limits.

1. Require the completed 155 actual-snake audit. Wait for existing proof jobs
   to finish; require at least 3 GiB free memory and one graph process. Use
   the native resource helper, without the old CIM monitor.
2. Reconstruct the 144 mask and bonuses without running its old optimizer.
   Reproduce its zero-credit weight hash and all 4,661,572 retained rows.
   Apply the selected floor vector and suffix-only maximum. Save hashes,
   match counts and changed-row counts. Recheck the saved cycles from their
   original source rows.
3. Check the saved range-602 potential on every new retained inequality
   \(496+\pi(v)\le W(e)+\pi(u)\). This establishes a feasible baseline.
4. Start every distance at zero and perform synchronous exact relaxation
   \(d'(v)=\min(d(v),\min_{e:u\to v}(d(u)+W(e)-496))\).
   Check integer overflow bounds. At stabilization, normalize by the minimum
   distance and check every edge again. Record a directed walk attaining the
   maximum deficit. Keep predecessor layers in a bounded-memory disk journal.
5. Save the potential, weight and input hashes, every-edge minimum slack,
   range, and the attaining deficit walk. Stop discovery after 600 seconds
   or 1,500 iterations. A timeout remains unresolved. A verified range-602
   baseline together with a walk of deficit 602 would already prove that
   this fixed-mean range cannot improve.

The zero initialization is a shortest-path calculation from a super-source
with zero-length edges to all vertices. Feasibility excludes negative cycles.
Its limiting minimum distance is the negative of the maximum directed-path
deficit. Every potential must have span at least that deficit. The normalized
stable distances attain it, so a complete convergence and an attaining walk
certify the minimum span at this fixed mean. Assert that the stable maximum
distance is zero as a consistency check. This claim requires the complete
finite relaxation and edge verification, not an iteration limit alone.

The immediate target is integer range at most 601. The comparison is

\[
235-\frac{632-R}{4696}.
\]

A smaller range improves the conditional 234 margin. The selected mean cap
and nonnegative range cannot give 233. A fixed-mean optimum does not settle
the best joint mean/range tradeoff. The pending local theorems, reference
refutations, exact graph interpretation and Lean edge certificate remain
separate after any numerical success. No paper rewrite is part of this task.
