# A count-sum restriction on the surviving cycles

Let \(\alpha_i\) denote the existing singleton-square count at vertex
\(x_i\). The proposed restriction is

\[
\alpha_{r+3}\le5
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge16
\]

when the six transitions starting at \(x_r\) have canonical pattern
\(012034\), with \(r+6\le m\). This means five distinct directions
\((a,b,c,a,d,e)\). No restrictions on the four outer counts are imposed
beyond their usual internal range. No new mathematical definition is needed.

## Why this restriction was selected

The two final cycles from milestone 115 contain this direction shape with
middle count five and outer sum fifteen. The completed-floor cycle has,
among others, the count tuples \((3,3,5,5,4)\) and \((3,4,5,5,3)\).
The conditional-floor cycle has \((5,2,5,4,4)\). The proposed inequality
therefore excludes an edge from both saved cycles. This provides a concrete
test affecting both comparison profiles. Removing those two particular
cycles alone does not prove that either minimum mean increases.

## Native contradiction and its remaining Lean obligation

Translate the initial vertex to zero and relabel coordinates. The selected
segment becomes \((0,1,3,7,6,14,30)\). Suppose the middle count is at most
five and the outer sum is at most fifteen. Each outer count is the number
of absent opposite corners in its 21-entry list. Concatenate the four lists,
preserving repeated corners. Their true-literal count is exactly the four
counts added together. Sorting these occurrences leaves that sum unchanged.

The necessary radius-four model rejects these assumptions without additional
cycle cuts. A complete native certificate was generated and independently
replayed by unit propagation. Its retained contradiction uses 5,662 input
clauses, 159,380 deductions and 13,252,922 antecedent references.

A further native proof on that extracted input has 142,180 deductions and
8,712,029 references. Its input clauses were checked against the original
full formula, and the contradiction was independently replayed after mapping
every input and deduction identifier to that formula. The selected proof
uses 1,709 distinct variables. The earlier proof and both solver attempts
are preserved.

Lean checks the transfer from an explicit local contradiction to the
displayed inequality for arbitrary matching snakes. That local contradiction
is still a hypothesis in the checked statement. The concrete joint-counter
interpretation, full Lean contradiction replay and final composition remain
pending. Consequently this milestone does not claim a completed Lean theorem
for the candidate inequality. The native replay and conditional geometric
transfer are separate evidence.

## Positive controls and unresolved stronger statements

The same local model admits counts \((5,3,5,3,6)\), with middle count five
and outer sum seventeen. An independent check verifies the selected vertices,
cube adjacencies, represented endpoint allowance, absence of cycles and all
five counts. Its selected graph has five components. It is a local forest;
it does not establish a complete snake with those counts.

The test with outer sum at most sixteen remains unresolved after its
15-second run. Thus this evidence places the minimum outer sum allowed by
the relaxed local model between sixteen and seventeen, without identifying
which value is attained. An outer lower bound of eighteen is already
incompatible with the checked local witness under these assumptions.

Two additional 12-second tests remain unresolved: an unrestricted five-count
total at most twenty, and the same total with all five counts at most five.
Their time limits prove neither feasibility nor impossibility. All earlier
outcomes are retained with their original status.

## Effect on the two finite comparisons

Add the proposed rule to the ten-rule experiment from milestone 115. Keep
the shared excess coefficients at 24. The new outer-four deficit is combined
with other applicable deficits by their maximum. This uses the existing
capacity \(4\cdot24+24=120\). Symbol six continues to represent the interval
\([6,21]\). A positive deficit deletes an edge only when all counts used
in the sum are exact; otherwise the deficit can require excess charge.

The added rule removes 23,285 further edges. A potential inequality is checked
on every retained edge in each profile, and a saved cycle attains its mean.
An independent bounded audit checks the full keys, accepted-diagram membership,
endpoints, weights, rule applicability, cycle chaining, potential bytes and
ranges, and arithmetic. It does not repeat the producer's all-edge scan.

| Share inputs | Minimum mean | Recorded potential range | Exact comparison | Integer part |
|---|---:|---:|---:|---:|
| Completed local floors | \(2915/6\) | \(1730/3\) | \(1324108/5623\) | 235 |
| Conditional floors | \(496\) | \(602\) | \(551765/2348\) | 234 |

The first mean increases by \(41/78\) from \(6309/13\), and its recorded
range decreases by \(478/39\). The conditional profile is unchanged. Both
refined graphs still assume unproved local rules; the completed-floor name
describes their share inputs. These calculations establish no new
unconditional upper bound for snakes.

The replacement cycles have eighteen and three edges. Every applicable
count deficit vanishes at both tested placements. Their weights therefore
remain unchanged under any admissible nonnegative redistribution of the
coefficients within this fixed eleven-rule family. The cycles give mean
ceilings \(2915/6\) and \(496\), and the saved balanced-coefficient
potentials attain them. Further coefficient searches within this family
cannot raise either mean.

The existing comparison is

\[
(4200d+p)m\le1098960d+8p+R.
\]

Lean checks that \(6p\le2915d\) leaves \(m=235\) compatible with this
inequality for every nonnegative \(R\). At zero range the scaled shortfall is
\(111960\cdot6-227\cdot2915=10055>0\). The conditional mean 496 similarly
leaves length 234 compatible, by the earlier checked comparison arithmetic.
Reducing the potential range alone therefore cannot improve these integer
conclusions.

## Next useful mathematical test

The replacement cycles both contain shape \(012301\), with truncated
tuples \((4,2,6,2,3)\) and \((4,2,6,4,2)\). Their outer four sums are exactly
eleven and twelve. Their middle counts range from six through twenty-one.
A lower bound of thirteen on the outer sum for this shape would affect
both cycles. It is an untested candidate; first check existing local
witnesses and then test outer sum at most twelve. If the unrestricted
claim fails, the recorded middle interval or individual outer caps may
identify a valid restricted statement.

The maintained interval remains \(191\le a(9)\le235\), using the archived
contributor upper-bound proof with its complete independent rebuild pending.
The reference union still has 1,366 outstanding entries. Conditional 234,
the exact optimum and the conjecture 196 remain unresolved. The manuscript
remains revision 116, with the next full revision scheduled for 126.
