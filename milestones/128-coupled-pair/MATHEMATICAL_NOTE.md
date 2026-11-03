# Applying the proved pair inequality to the six-count test

The target remains

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge 23
$$

for an actual snake window with canonical direction pattern 0120324. This
statement is unproved. Its failure would give a six-count total at most 22.
The existing necessary intervals for such a counterexample are

$$
([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).
$$

The new search also uses the previously proved inequality

$$
\alpha_{r+2}+\alpha_{r+4}\ge 8.
$$

This follows from the canonical prefix 012032. It holds without assuming
that the six-count total is at most 22. No additional mathematical definition
is needed.

## Counting the pair correctly

Translate and permute the coordinates so that the eight window vertices are

$$
0,1,3,7,6,14,10,26.
$$

At the second internal centre, the vertex is 3 and the two path directions
are 1 and 2. At the fourth, the vertex is 6 and the directions are 0 and 3.
Each centre has 21 opposite corners formed by flipping two of its seven
unused directions. By the established interpretation of the singleton-square
count, exactly \(\alpha_{r+2}\) and \(\alpha_{r+4}\) of these corners,
respectively, are absent from the snake.

The two lists contain 42 occurrences over 37 distinct vertices. The common
vertices are

$$
18,34,66,130,258.
$$

Each common vertex contributes once to each count. Thus the number of selected
occurrences is exactly

$$
42-\alpha_{r+2}-\alpha_{r+4}\le34.
$$

Removing repeated vertices would change the quantity and invalidate this
conversion. The implementation retains all 42 positions.

## Search and proof requirements

The added constraint bounds the selected occurrences by 34. Its sequential
counter introduces 1428 variables and 2863 clauses. Appending it to the reduced
input from milestone 127 gives 104529 clauses and 6248 occurring variables.
Existing variable identifiers are retained; the largest identifier is 8705.

The geometric pair theorem justifies this additional constraint for actual
snakes. No derivation of these clauses from the old search input alone is
claimed. A final contradiction must therefore be checked against the new
input, with the pair theorem included in the interpretation. The old
original-input identifier mapping cannot simply be reused for the new clauses.

The remaining distinction is substantive: a checked interpretation of this
constraint does not prove that the six-count total exceeds 22. That conclusion
requires a complete refutation of the combined constraints. A bounded search
that returns no result leaves the target open.

## Next reduction within the same route

The established restrictions permit an exhaustive split according to whether
\(\alpha_{r+4}=3\) or \(\alpha_{r+4}\ge4\). In the first case, the
proved pair inequality gives \(\alpha_{r+2}\ge5\). The earlier exclusion
of \(\alpha_{r+1}\le2\) together with \(\alpha_{r+4}\le3\) also gives
\(\alpha_{r+1}\ge3\). Consequently, a counterexample in that case satisfies

$$
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\le11.
$$

These are arithmetic consequences of the saved theorems, suitable for a more
restricted search. They are recorded as the next task; the present checkpoint
does not claim that either branch has been excluded. Both branches must be
addressed to prove the six-count target.

An exhaustive integer enumeration satisfying just these necessary inequalities
leaves 1287 count vectors in the equality case and 14014 in the other case.
Independent binomial counts agree. This makes the equality case the smaller
first test. These are counts of integer vectors; geometric realizability is
not asserted. The enumeration and its exact scope are saved in
`data/next-split-counts.json`.

Even a proof of this single-pattern target would only remove the sum-22 edge
of the saved conditional comparison cycle. It would not establish a universal
six-count bound or a new global upper bound. The maintained interval remains
\(191\le a(9)\le235\), subject to the previously documented independent
rebuild limitation on the contributor upper-bound proof. The optimum and 196
remain unresolved.

## Verification in this round

Two Lean modules passed with ten dependency reports, all using only
`propext`, `Classical.choice`, and `Quot.sound`. They verify the actual count
conversion, normalization, and satisfaction of the 2863 added clauses. A
separate parser confirms that the checked source contains exactly the new
clauses, literals, tags, and variable meanings used in the search. The complete
conjunction with the older input is outside these two modules' scope.

The native run timed out after 180.062 seconds, using 24.59375 seconds of CPU
time. Its first 1000 deductions were independently replayed against the new
input, with no empty clause in that prefix. The full partial trace is preserved
in a lossless archive. These checks establish no new six-count floor.

The next split above is a written deduction from checked premises. Its new
actual-snake assembly remains to be checked in Lean before the next branch
exclusion is claimed.
