# Testing a weaker local assumption

The proposed change is to lower the conditional012034 share floor from18
to17, retaining the other milestone156 assumptions and weights. The
hypothesis is that a potential with mean496 and range at most631 still
exists. Such a certificate would preserve the comparison below235 and
reduce the unresolved local share requirement by one. Feasibility remains
unresolved until a new all-edge certificate is checked.

The previously accepted nine-edge walk loses exactly one unit, so its
weight becomes3861. At mean496 it requires range at least603. The retained
fourteen-cycle is unchanged and still bounds the mean by496. A successful
integer range at this mean must therefore lie between603 and631 inclusive.

## Why the saved potential needs individual state changes

Let p be the saved range602 potential. Its transformed values t*p+b obey
two necessary edge inequalities under the weaker floor:

    mu <=377+118t,       mu <=616-120t.

The first is the changed edge4684655; the second is edge491026. For any
real scaling, the transformed range R=602*abs(t) satisfies R>=602t.
The two inequalities and this range inequality imply

    227mu-111960-R <= -10351/119 <0.

Thus for nonnegative mean and nonnegative uniform occurrence credit C,
the comparison (1098960+8mu+24C+R)/(4200+mu) is strictly greater than235.
No shift or scaling of the saved potential can retain the target. Lean
checked this rational implication, the weaker-walk range bound, the target
range equivalence and the automatic mean495 transfer calculation, five
statements in total. Source, compiler output and dependencies are pinned
in data/affine-lean-check.json. The edge values themselves come from the
selected-row audit, separate from these arithmetic checks.

The automatic transfer to mean495 remains feasible because each edge loses
at most one unit, but its comparison is235+197/4695. This does not preserve
the conditional234 conclusion.

## Rejected earlier obstruction

The old51-edge floor17 walk survives the retained mask, but its old weights
do not survive the current count bonuses. Recalculation on its saved row
data adds1056, changing its deficit from633 to-423. It therefore supplies
no obstruction to the proposed test. This limited check is documented in
milestone156/review/next-step-review.md; the51 original graph rows were not
independently reloaded for that review.

## Required computation and scope

Reconstruct and hash-check the accepted156 weights before applying the one
floor change. Test potentials allowing individual state values to change.
Accept feasibility only after checking every retained inequality exactly.
A checked walk with deficit at least632 rules out the target at mean496.
A resource stop or timeout leaves the question unresolved.

All remaining local floors, count restrictions, reference refutations and
graph-to-snake interpretation remain obligations. Neither the arithmetic
above nor a future finite certificate supplies a new unconditional bound.
No new mathematical definition is needed for this investigation.
