# Potential certificates on the defined graph

Both saved potentials satisfy every edge inequality of the graph used by the
Lean interpretation. The independent enumeration finds exactly 4,947,008
accepted full keys, with no extra or missing keys relative to the saved graph.
This equality and the full edge scan are numerical results. Lean has checked
the concrete potential ranges, the interval-checking argument, the resulting
upper-bound statements with explicit finite-check assumptions, and the finite
checks recorded below. No new global numerical bound follows from this round.

## Mathematical argument

Use the existing edge weights and potential notation. For an edge $e:u\to v$
with weight $w_e$, the required inequality is

$$P+\pi(v)\le w_e+\pi(u),\qquad 0\le\pi\le R.$$

In this display the edge retains its complete direction, history and count
key; endpoint pairs alone need not identify its weight. Summing along the
$m-8$ graph edges of a snake gives

$$P(m-8)\le W+R.$$

Milestone 98 proves $W+4200m\le1098960$ for $m\ge9$. Hence

$$ (4200+P)m\le1098960+8P+R. $$

The completed profile has $P=483$ and $R=551$, giving
$4683m\le1103375<4683\cdot236$. The conditional profile has $P=496$ and
$R=602$, giving $4696m\le1103530<4696\cdot235$. The respective conclusions
are $m\le235$ and $m\le234$ after their remaining hypotheses are supplied.
The cases $m<9$ are immediate and included in the checked bound statements.

## Evidence obtained

The numerical checker reads the diagram and rule tables from Lean source
literals. It checks all 791 assigned contexts and all 127 shared acceptance
classes. The completed potential has 1,288,037 tight accepted edges; the
conditional potential has 1,828,136. Both have minimum slack zero.

The saved potentials are represented by shared six-way trees: 20,234 internal
nodes for the completed profile and 9,612 for the conditional profile, with
206 root positions each. A separate parser expands the actual generated Lean
literals and verifies all 3,203,712 entries against the original arrays.
Every entry agrees. Lean accepts the candidate definitions and proves their
range bounds for all natural state indices. Capping at the stated range
supplies this bound; the independent expansion confirms that the cap changes
none of the saved values.

Lean also verifies the accelerated diagram lookup against the original
diagram evaluation. The interval checker is proved sound and supports joining
adjacent intervals, transferring equal tests, and assembling complete
contexts. Missing context assignments are handled symbolically. The final
assembly uses these exact candidate potentials; it has no free potential or
range premise.

Both pilot intervals $9720\le c<11880$ passed Lean. The completed test uses
direction 35 and history 0, containing 143 accepted edges. The conditional
test uses direction 177 and history 43, containing 64 accepted edges. Rejected
codes impose no edge inequality. Smaller earlier pilot intervals lie inside
these intervals and are not additional coverage.

Complete-context Lean checks remain pending. Unfinished modules and their preserved attempts are listed in the proof summary; no failed or timed-out attempt proves its statement. The CompletedContext99 attempt reached the 300-second limit. ConditionalContext99 was not started.

The exact successful modules, axiom reports, timings, source snapshots and
dependency hashes are recorded in `data/proof-summary.json`. Existing proof
objects and the milestone 98 object overlay are reused. This is not a clean
rebuild of every inherited proof dependency.

## Remaining proof obligations

The completed upper-bound assembly retains two reference-catalogue closures
and the Boolean certificate for every graph edge. The conditional assembly
also retains the five local refutations with caps $(15,17,15,15,15)$, or share
floors $(16,18,16,16,16)$, in case order 7301, 7302, 7303, 7307, 7308.
The complete finite edge certificate is still pending in Lean for both
profiles. Numerical success and individual context checks do not discharge it.

The original case7302 proof attempt, which targeted share 20, remains stopped
and unchanged. A proof of the weaker required share 18 must have separate
sources and evidence.

## Next step

Continue the finite potential verification using the checked interval
interface. Before expanding the batch, specialize the computations that are
constant in each direction/history context and measure a bounded test.
Traverse the acceptance diagram by shared prefixes and skip a branch as soon
as it reaches the rejecting leaf. This avoids restarting the same six-step
lookup for each of the 46,656 codes. Its soundness proof must retain the exact
prefix encoding and original acceptance predicate.
Repeated loading and reduction of the complete semantic environment may be
avoidable; any lighter evaluator must have a proved equality or valid
one-sided comparison with the current weight.

Independent comparison groups the 791 contexts into 582 joint classes of
identical acceptance roots, ordered potential blocks and complete weight
arrays. Every repeated array was compared directly after hash grouping.
This can remove 209 pairs of context checks once the corresponding Lean
equalities and transport are proved. Acceptance classes or endpoint pairs
alone are insufficient for that reuse.

The maintained interval remains $191\le a(9)\le235$ edges, with 234 conditional.
The contributor upper-bound theorem retains its archived audit and pending
independent rebuild. The exact optimum remains unresolved. Paper revision 96 is unchanged;
the next full revision is scheduled for milestone 106.
