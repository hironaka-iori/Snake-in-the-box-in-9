# Restriction from the surviving fourteen-cycle

This note concerns the fixed graph comparison. It establishes no new upper
bound for arbitrary snakes. The saved-row and rational calculations were
rechecked; the new arithmetic implication below awaits Lean verification.

The older three-cycle from milestone 149 cannot be used unchanged in the
later retained graph: two of its three edges were removed. The fourteen-cycle
reviewed in milestones 144, 145 and 153 survives and contains no canonical
012032 window at any of the four six-transition positions, in either
orientation. Consequently a weight increase confined to 012032 cannot
change this cycle directly.

Use the existing notation F and G for the 012301 and 012340 share floors.
In the preserved affine regime F >= 11 and G >= 4, with all other weights
fixed, the cycle and its first two edges imply

\[
7\mu\le3424+2F+G,\qquad 2\mu\le496+F+R.
\]

The comparison is

\[
\frac{1098960+8\mu+24C+R}{4200+\mu},\qquad \mu,C\ge0.
\]

At F=G=16, these constraints give \(\mu\le496\) and
\(R\ge2\mu-512\). Therefore

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{1098448+10\mu}{4200+\mu}
\ge\frac{137926}{587}
=235-\frac{19}{587}
=234+\frac{568}{587}.
\]

The second fraction decreases for nonnegative \(\mu\), since the sign of
its derivative is the sign of \(42000-1098448<0\). The endpoint value is
already present in the milestone-145 saved calculations. Unlike its stronger
two-cycle restriction, this lower bound does not retain the obsolete
eleven-cycle baseline. It remains applicable when only 012032 weights change.

A comparison below 235 is still possible in this arithmetic relaxation;
existence of a valid potential for the full graph remains separate. A
comparison below 234, as required by this route to certify an upper bound
of 233, is impossible while these constraints remain unchanged.

More generally, a comparison below 234 would require

\[
115664-F+24C<224\mu.
\]

Combining this with the cycle cap gives the necessary condition

\[
455F+224G>42672+168C.
\]

For F=16 and C>=0 this requires G>158. This calculation only identifies
a limitation of the fixed comparison and cycle weights. It does not assert
that such floors are attainable, sufficient, or required by other methods.

The practical next step is to finish the share-17 proof and inspect the
remaining full-graph potential obligations for 234. Further work towards
233 must also change the surviving fourteen-cycle constraints or the
comparison formula. Increasing only the 012032 floor cannot achieve that
target within this fixed model.

Evidence: range-scope-review.json. Its saved-row extraction is inherited from
the pinned prior audits; this round did not reload every graph array.
