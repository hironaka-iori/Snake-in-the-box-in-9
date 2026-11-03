# The fourth count equal to three

Consider an induced path in the nine-dimensional cube and a fitting window
whose canonical direction sequence is 0120324. All counts below use the
existing singleton-square notation. The target remains

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge23.
$$

This target is still unresolved. The present round isolates a stronger local
statement that would settle one of its two remaining cases:

$$
\alpha_{r+4}=3
\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

The finite contradiction supporting this implication has passed independent
Python replay. Its complete Lean verification remains pending. In particular,
the implication is a candidate result at this checkpoint.

## Why this case is sufficient to examine first

The earlier results imply that a counterexample with six-count total at most
22 has \(\alpha_{r+4}\ge3\). Thus either the fourth count equals three or
it is at least four. Lean checks this split and the following deductions.

The prefix 012032 gives

$$
\alpha_{r+2}+\alpha_{r+4}\ge8,
\qquad
\neg(\alpha_{r+1}\le2\ \text{and}\ \alpha_{r+4}\le3).
$$

When \(\alpha_{r+4}=3\), these imply
\(\alpha_{r+1}\ge3\) and \(\alpha_{r+2}\ge5\). Consequently, a
six-count total at most 22 would force

$$
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}
\le22-3-5-3=11.
$$

The branch search returned a complete contradiction. Inspection of the
constraints actually used revealed that the contradiction needs only the
fourth count equal to three and the last displayed triple total at most
eleven, together with necessary induced-path constraints. It uses no
six-count upper bound, pair-count premise, or strengthened first or second
count. This is the basis for the stronger candidate implication.

## Interpretation of the three counts

After translating the initial vertex to zero and permuting coordinates, the
window vertices are

$$
0,1,3,7,6,14,10,26.
$$

The three relevant internal centres are 7, 14 and 10. Their incident path
directions are respectively \((2,0)\), \((3,2)\) and \((2,4)\). At
each centre, choose two of the seven unused directions. The 21 resulting
opposite corners contribute to the existing singleton-square count exactly
when they are absent from the snake.

The concatenated lists therefore contain 63 occurrences. Repeated vertices
retain their multiplicities, since a vertex can contribute to more than one
centre. The number of absent occurrences is exactly

$$
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}.
$$

Lean checks the general conversion from these occurrences to the actual
three counts. The concrete input uses that conversion under the contrary
hypothesis that their sum is at most eleven. No assumption about the other
three counts is required for this conversion.

## What the certificate establishes and what remains

The selected finite input has 3500 clauses. Its refutation has 50082 deductions
and 2628221 ordered hints. Independent checks replay the native proof,
the reductions, the variable renaming, and the packed exported proof through
the final empty clause. Every selected input also has a saved geometric or
counter justification tag.

Two remaining requirements are checked separately: every selected clause
must hold under the assignment obtained from an actual snake satisfying the
contrary hypotheses, and Lean must accept the entire selected refutation.
The generic actual-snake count conversions and the concrete interpretation
have passed in Lean. Lean also checks both deductions below conditional on
the contradiction of this exact input. The complete refutation is still
running; its partial progress and the independent Python replay do not
establish the unconditional local implication.

Once both requirements pass, the candidate implication gives

$$
\sum_{j=1}^{6}\alpha_{r+j}
\ge3+5+3+12=23
\qquad\text{when }\alpha_{r+4}=3.
$$

This would leave only \(\alpha_{r+4}\ge4\) in a counterexample to the
six-count target. That complementary case is still open. The claim for this
single direction pattern would itself remain insufficient for a universal
six-count bound or a new global upper bound.

The maintained interval is \(191\le a(9)\le235\), with the previously
recorded independent-rebuild limitation on the contributor upper-bound
proof. The optimum and the proposed value 196 remain unresolved.

## Continuation

Complete the current Lean contradiction and its actual-snake interpretation,
then combine them explicitly. Afterward test the remaining fourth-count-at-
least-four case using only premises valid in that case. The first-count lower
bound three and second-count lower bound five above cannot be carried into
that case without another proof. Keep any improved conditional or
unconditional global bound separate from this local exclusion.

No new mathematical definition is introduced. The paper remains at revision
126; the next scheduled full revision is 136.

## Completed endpoint result

The earlier endpoint proof finished during this research period. For every
fitting canonical 012032 window with
\(\alpha_{r+2}+\alpha_{r+4}=8\), both centres have Hamming distance two
from both endpoints. There are at most thirteen such starts in a snake.
All local certificate premises are discharged in the final Lean theorem.
The independent completion audit verifies all 448 modules and 30 axiom reports.

The occurrence bound follows because the two endpoints have at most fourteen
common vertices at distance two. For a nonempty finite set of qualifying
starts, the centres at positions \(r+2\), together with the centre at
\(\max(r)+4\), are distinct vertices of that intersection. Thus the number
of starts plus one is at most fourteen. Here the maximum is taken over the
qualifying starts.

This can restrict repeated equality windows in the global argument. The
required correspondence between those occurrences and the global counting
inequality remains a separate proof obligation. No numerical improvement
of the global upper bound is inferred from this completion alone.
