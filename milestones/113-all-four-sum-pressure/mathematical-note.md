# Pair counts on the surviving six-step window

This round continues the count-sum argument for the empty-square charge.
It introduces no mathematical definitions. The counts, clipping at 6,
direction patterns and charging constants retain their earlier meanings.

## Candidate inequality and its evidence

Consider a six-step window whose canonical direction pattern is
`012034`. Its five internal counts, in order, are
\(\alpha_{r+1},\ldots,\alpha_{r+5}\). The candidate is

\[
\alpha_{r+2}\leq5,\qquad
\alpha_{r+3}\leq4,\qquad
\alpha_{r+4}\leq5
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+5}\geq9.
\]

The radius-four solver reports that the premises together with an outer
pair sum at most 8 are unsatisfiable. This run uses no additional cycle
cuts. It remains an uncertified native result. Two subsequent attempts
to generate a complete proof each reach their 30-second limit. Their
partial files are retained, and neither is a contradiction certificate.

Lean checks the geometric transfer to an actual snake under an explicit
local contradiction premise. The missing concrete contradiction remains
visible in the theorem's assumptions. Consequently this round does not
establish the displayed candidate for every snake.

The native exclusions for count caps \((4,4,4,4,4)\),
\((4,4,4,5,4)\), and \((4,5,4,5,4)\) are consistent with the
candidate. Exact count tuples \((4,4,4,4,4)\) and
\((4,3,4,5,4)\) are also excluded by native runs. These statements
have the same certificate limitation. The sum test is broader than the
box with caps \((4,5,4,5,4)\), since it covers every split of an
outer pair sum at most 8.

## Local limitation

A saved local configuration has exact counts

\[
(6,5,4,5,3).
\]

It satisfies the three central caps and has outer sum 9. An independent
check reconstructs its cube adjacencies, radius-four domain, degrees,
interior endpoint allowance, components and counts. It has no cycles.
Thus the same local hypotheses cannot imply an outer sum of 10 in this
relaxed model. The lower threshold 9 still needs its contradiction proof.

Two further local configurations have counts \((10,4,4,3,6)\) and
\((5,5,4,5,5)\). They prevent treating the respective relaxed boxes
as impossible. All three configurations have relaxed boundary conditions;
they do not construct complete long snakes or settle what a connected
snake can realize.

## Shared charging argument

For nonnegative integers \(x,y,L\) with \(L\leq x+y\),

\[
\max\{0,L-\min(6,x)-\min(6,y)\}
\leq (x-\min(6,x))+(y-\min(6,y)).
\]

This follows by subtracting the clipped counts from the assumed lower
bound and using nonnegativity. Lean checks this inequality. It also checks
that a pair deficit can be included by taking the maximum with the
previous window credit, using the same coefficients \(a,b\geq0\)
and capacity condition \(4a+b\leq120\).

For a suffix window, the outer pair occurs at positions \(r+4,r+8\).
Its two excesses are included among the four outer excesses already
charged with coefficient \(a\). Each excess occurs in at most four
outer positions and one central position when summing over windows.
Therefore the maximum of the previous credit and the weighted pair
deficit remains bounded by 120 times the total excess above clipping at
6. Credits from different rules are combined by a maximum. Summing them
would require a separate budget argument.

The local pair lower bounds remain hypotheses in this generic argument.
The checked boundary contribution from milestone 112 remains 21, or 2520
after scaling. No concrete global integration is supplied by this round.

## Effect on both finite graph comparisons

The baseline for comparison is the seven-rule experiment in milestone
112, with 4,909,227 surviving keys. Each key includes direction, history
and count code. Parallel keys remain distinct. A count symbol 6 represents
the interval from 6 through 21, so a cap of 4 or 5 cannot be applied to it.
Both placements and both orientations are accounted for. The pair rule's
conditions and sum positions are invariant under reversal.

| Additional hypothesis | Further keys removed | Remaining keys | Completed mean and range | Conditional mean and range |
| --- | ---: | ---: | --- | --- |
| Box caps \((4,5,4,5,4)\) are impossible | 21,877 | 4,887,350 | 484 and 557 | 496 and 602 |
| Central caps \((5,4,5)\) imply outer sum at least 9 | 41,361 | 4,867,866 | 484 and 557 | 496 and 602 |

These are conditional finite graph calculations. The first profile uses
the previously completed share floors; the second uses the stronger
conditional floors. Both experiments additionally assume the unproved
count restrictions. Neither becomes an unconditional snake bound merely
because the profile is named `completed` in the saved data.

For balanced coefficients \(a=b=24\), the pair experiment gives

\[
\frac{1098960+8\cdot484+557}{4200+484}
=\frac{1103389}{4684},
\qquad
\frac{1098960+8\cdot496+602}{4200+496}
=\frac{551765}{2348}.
\]

Their integer floors remain 235 and 234. Integer potential inequalities
were checked over every retained edge, with attaining cycles saved in
both profiles. This is a native exhaustive graph check; a complete Lean
certificate for the modified graph remains pending.

The replacement completed cycle has nine edges, with weights
\(720,360,492,600,360,372,600,480,372\), summing to 4356.
The replacement conditional cycle has four edges, with weights
\(616,618,252,498\), summing to 1984. Every applicable count deficit
on these cycles vanishes. Thus their means remain 484 and 496 for every
nonnegative coefficient choice within this fixed eight-rule family.
Balanced coefficients attain both ceilings. Another coefficient sweep
within this family cannot improve either mean.

Milestone 112's checked comparison arithmetic also shows that, at these
mean ceilings, reducing a nonnegative potential range alone cannot rule
out lengths 235 and 234 respectively.

## Consequences for the next round

The old limiting cycles have been removed, while replacement cycles
retain their means. The priority is to test exact windows on those
replacement cycles and seek a broader inequality that they violate.
The pair threshold cannot be increased to 10 using the current relaxed
local assumptions, and its existing certificate attempts should remain
preserved. Expensive proof generation should follow a demonstrated
improvement in at least one finite comparison or another specific use
for the theorem.

A precise next test is the total of the five counts on `012310`.
The replacement completed cycle contains tuples \((3,4,5,3,3)\)
and \((3,3,5,4,3)\); the conditional cycle contains
\((2,4,5,5,2)\). Each sums to 18. A lower bound of 19 would therefore
remove an edge from each saved cycle. Such an inequality is untested
in this round, and removing these cycles need not improve the optimum:
other attaining cycles may survive. Test total at most 18 first, without
extra count caps, then evaluate any viable result on both full profiles.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit; its complete independent rebuild
remains pending. Conditional 234, the exact optimum and 196 remain
unresolved. The paper remains at revision 106, with its next full revision
scheduled for 116.
