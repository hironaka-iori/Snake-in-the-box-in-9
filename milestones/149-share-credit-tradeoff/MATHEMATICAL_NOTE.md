# Uniform occurrence credit and the original share profile

The attempted tradeoff is impossible within the specified graph argument:
the 012032 share floor cannot be lowered from 16 to 15 by retuning the
existing uniform occurrence credit. This strengthens the earlier result
that tested the floor only at zero credit. It does not give a new bound
for arbitrary snakes.

## Exact setting

Use the original 4,947,008-edge graph and 1,601,856 states from the milestone
72 full-key construction, with the same base weights and maximum rule used
in the milestone 97 floor sensitivity calculation. In shape order
012031, 012032, 012034, 012301, 012304, 012310, 012314, 012340, 012345,
fix the floors at

\[
(16,15,18,16,16,12,16,16,16).
\]

An edge receives credit \(C\ge0\) precisely when its suffix has shape
012032 and its second and fourth internal count symbols are both below six
and sum to at most nine. The occurrence allowance in the comparison is 24.
These exact symbols represent actual counts. The occurrence theorem is
an existing result; the experiments do not establish a new occurrence bound.

For a nonnegative potential mean \(\mu\) and a potential range \(R\),
the existing comparison is

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}.
\]

## Obstruction for every credit

The unchanged three-cycle has weights 616, 496, 376 and no credited event.
The eleven-cycle has four credited events and weights, before that credit,

\[
375,496,495,496,496,376,616,495,496,495,616.
\]

Their sum is 5452. The newly extracted 28-edge walk has weight 13280 and
no credited event. Telescoping the edge inequalities around the cycles
and along the walk gives

\[
\mu\le496,\qquad11\mu\le5452+4C,\qquad28\mu\le13280+R.
\]

Consequently \(24C\ge66\mu-32712\) and \(R\ge28\mu-13280\), so

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge235+\frac{65968-133\mu}{4200+\mu}\ge235.
\]

The last inequality uses \(65968=133\cdot496\) and the positive denominator.
Equivalently, a comparison below 235 would require both \(C<1\) and
\(C>1\). Equality in these three numerical constraints occurs at
\(\mu=496,C=1,R=608\). No full-graph potential attaining that equality
has been constructed or claimed.

Lower 012032 floors also fail in this fixed comparison, by monotonicity:
their edge weights are no greater, so any potential valid for them would
also be valid for floor 15. This statement keeps the other eight floors,
graph, event and boundary expression fixed. In particular, it does not
extend without further work to later graphs with removed edges or increased
weights. The original share-16 sufficient profile remains unaffected.

## Checks and failed candidate

The first bounded test lowered the share floor and added credit one while
reusing the old range-602 potential. Of 66,567 decreased edge weights,
43,003 did not receive the occurrence credit. There were 21,861 violated
potential inequalities. This result alone rejected only that saved potential.

A second bounded exact-integer calculation tested the same profile at
mean 496. It extracted the 28-edge walk with deficit 608. At credit one,
its deficit together with the boundary cost 24 reaches the limiting 632.
The eleven-cycle then extends the obstruction to every credit. No additional
credit value, solver or graph optimization was needed.

The saved input arrays, shape recognition, full edge keys, endpoints,
weights and event indicators are independently reviewed in
`audit/graph-review.md` and its machine-readable companion. The result is
finite-array evidence combined with checked arithmetic. The five accepted
Lean statements use only `propext`, `Classical.choice` and `Quot.sound`.
They take the cycle and walk inequalities as explicit premises; the actual
graph is not encoded in this new Lean module. External Lean and Mathlib
libraries are trusted with the recorded entry artifacts and hashes.

## Continuation

Keep the existing 012032 share-16 target. Do not spend another round
retuning this uniform credit to compensate for floor 15 on the same graph.
The selected continuation remains the 012301 cap-15 contradiction replay
already running in milestone 147. Its same coordinator resumed after the
small arithmetic check. When its complete 1,789-module replay succeeds,
audit the final contradiction and check the prepared milestone 148 final
composition. The conditional coordinate and reversal transfer is already
checked and must not be restarted.

The other pending local floors, reference premises, graph interpretation
and potential obligations remain separate. The maintained interval is
\(191\le a(9)\le235\), using the contributor upper theorem whose complete
independent rebuild remains pending. The optimum and 196 remain unresolved.

Both existing paper copies contain the new proposition. Authors and
preamble are unchanged, with no new definition. The built-in PDF compiler
again failed before TeX processing in its Windows helper. No PDF rebuild
or layout check is claimed. The last full paper revision was 146; the next
is due at 156. Goal active.
