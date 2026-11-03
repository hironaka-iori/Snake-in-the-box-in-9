# A restriction on four outer singleton-square counts

Let $p_0,\ldots,p_m$ be a snake in $Q_9$, and retain the manuscript notation
$\alpha_i$ for the number of coordinate squares containing $p_i$ and no other
vertex of the snake. Suppose the six directions beginning at $p_r$ are
$(a,b,c,a,d,b)$, with $a,b,c,d$ pairwise distinct and $r+6\le m$. Then

$$
\max\{\alpha_{r+1},\alpha_{r+2},\alpha_{r+4},\alpha_{r+5}\}\ge4.
$$

There is no additional hypothesis on $\alpha_{r+3}$ or the length of the snake.

## Proof and its checked scope

Translate $p_r$ to zero and relabel the four coordinates in order of first
appearance. The seven window vertices become

$$
(0,1,3,7,6,14,12).
$$

Assume that all four displayed outer counts are at most 3. The middle vertex
is internal, so the existing general bound gives $0\le\alpha_{r+3}\le21$.
The five internal count intervals are therefore

$$
([0,3],[0,3],[0,21],[0,3],[0,3]).
$$

Every actual snake induces a satisfying assignment of the existing local
geometric encoding with these intervals and radius three. This implication
includes the coordinate normalization and count interpretation. The resulting
Boolean formula has 946 variables and 25,388 clauses. Its selected contradictory
core uses 2,552 input clauses. Lean checks the 5,956 deductions and 344,241 hints
leading to the empty clause, and hence rules out the assumed four count caps.
This is a finite checked proof; a short geometric derivation has not been found.

The actual-snake theorem has no unproved local-refutation premise. Its printed
dependencies use only the standard foundations reported in the final receipt
audit. The same contradiction gives both orientations of the encoded graph
restriction. The geometric implication, concrete clause check and contradiction
replay are separate checked steps; a solver's negative answer alone is unused
as proof.

## Consequences for the saved reference cases

The three reference tuples

$$
(2,3,6,3,2),\qquad(2,3,6,3,3),\qquad(3,3,6,3,2)
$$

all have direction pattern $012031$. The symbol $6$ denotes the complete
interval $[6,21]$. In each tuple it occurs at the unrestricted middle position,
while the four outer intervals lie in $[0,3]$. The new theorem therefore excludes
all three. Lean checks this containment, their reference indices 126, 127 and
138, and the remaining count $1378-15=1363$. The previous twelve exclusions are
retained. This reduces the pending reference premise; it does not discharge it.

## Effect on the upper-bound computations

The original target has nine directions $012031043$ and six recorded count
symbols $(6,3,3,6,3,3)$ at centres 3 through 8. Its final six directions
canonicalize to $012031$, with outer counts all equal to 3. The theorem excludes
this target without replacing any $[6,21]$ interval by an exact value.

Adding the exclusion to the inherited thirteen-rule experiment removes 63
further edges. Two belonged to its former conditional cycle. The recalculation
finds a five-cycle with the same mean, so the numerical comparisons do not change:

| Profile | Minimum cycle mean | Potential range | Edge comparison |
| --- | ---: | ---: | ---: |
| Completed-share profile with pending sum rules | $2915/6$ | $1730/3$ | $m\le235$ |
| Conditional-share profile with pending sum rules | $496$ | $602$ | $m\le234$ |

The exact comparison values are $1324108/5623$ and $551765/2348$, respectively.
The producer checks every retained edge inequality. The independent review
checks the 63 additional removals, both orientations, saved cycles, potential
bytes and comparison arithmetic. It does not repeat the complete edge scan.
The profile names refer to share catalogues. Both current experiments retain
unproved sum hypotheses and incomplete global Lean assembly.

The surviving cycles have no common six-transition direction pattern among
their recorded five-count windows. They also have zero deficits under all
thirteen inherited sum rules. Within that rule family, changing their
coefficients cannot increase the weight of either saved cycle. A further
improvement requires a restriction or charge that changes a surviving cycle,
or a stronger global argument. No additional definition is needed to express
this limitation.

## Sharpness and continuation

There is a radius-three induced forest with five counts $(4,4,13,4,4)$.
It has six components of sizes 36, 19, 25, 10, 7 and 7. Its geometry and
boundary conditions were independently checked. It shows that the corresponding
local relaxation cannot force the outer maximum above 4. It is disconnected,
and no extension to an actual snake is established. The full-cube search for
outer maximum at most 4 is UNKNOWN after 20.032 seconds and 31 cycle cuts.
Two asymmetric stronger exclusions have native negative answers only; they
are recorded as probes and have not been used as theorems.

The saved bank contains 131 complete snakes. Rechecking their induced paths
requires 2,402,016 vertex-pair tests. All pass. Among 868 occurrences of $012031$,
the smallest outer maximum is 7. This is a property of the finite bank and
does not prove a stronger lower bound for all snakes.

The next selected test is the nine-transition word $012031041$ from the new
conditional cycle, with six counts $(4,4,3,5,4,4)$ at centres 3 through 8.
Testing all six counts simultaneously may detect an obstruction lost when
separate five-count windows are considered. Its full-Q9 input is saved and
untested. Any successful restriction must be evaluated against both profiles.

The maintained global interval remains $191\le a(9)\le235$, with the contributor
proof and archived audit for 235 and its full independent rebuild still pending.
Neither 234 nor an exact optimum is established by this milestone.
