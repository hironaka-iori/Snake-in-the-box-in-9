# Count-sum restrictions and a shared excess budget

This round continues the empty-square argument using the existing counts
\(\alpha_i\). No new mathematical definition is required. Lengths of
snakes are measured in edges.

## A sum restriction for actual snakes

Suppose six consecutive transitions starting at \(x_r\) have canonical
directions \((0,1,2,3,1,4)\). Then

\[
\alpha_{r+3}\le2
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge19.
\]

The window must fit inside the snake, so \(r+6\le m\). The statement
has no collective reference-catalogue premise.

Translate the first vertex to zero and relabel coordinates. The window
becomes \((0,1,3,7,15,13,29)\), with the same five counts. Suppose the
middle count is at most 2 and the outer sum is at most 18. The actual
induced path supplies the selected vertices, degree conditions, endpoint
budget and acyclicity conditions in the radius-four local model.

Each outer count is represented by 21 negative corner literals. Their
concatenation has 84 occurrences involving 70 distinct literals. A vertex
may contribute to several counts, so those occurrences must retain their
multiplicities. Sorting preserves the represented sum. The checked
counter interface identifies its true-literal count with the sum of the
four absent-corner counts.

The resulting contradiction uses 3,306 clauses, 7,020 deductions and
367,588 propagation hints. A bijection moves the 1,718 variables used by
the proof into the supported range without changing the constraints.
The full formula, the bijection, the selected clauses and the contradiction
have been independently reconstructed or replayed. The geometric transfer
preserves the four actual counts at positions \(r+1,r+2,r+4,r+5\).

The contradiction and actual-snake composition pass Lean. Together with
the counter semantics, geometric transfer and shared budget, this round
has 40 successful module records and 20 printed standard axiom reports.
A complete rebuild of historical dependencies remains a separate task.

## Combining four-count and five-count inequalities

The previous completed profile's fourteen-edge cycle and conditional
profile's three-edge cycle both contained the exact tuple
\((4,3,5,4,3)\), with different direction patterns. Its five counts sum
to 19. This suggested a lower bound 20
for the sum on patterns \(012034\) and \(012031\).

The local solver rules out a total at most 19 on \(012034\). The same
unrestricted test on \(012031\) remains unresolved. On that second
pattern, a narrower test rules out an outer sum at most 14 when the
middle count is at most 5. The final graph experiment uses the following
family. Except for the actual-snake theorem above, the listed lower bounds
still require checked contradiction certificates and geometric transfer.

| Direction pattern | Condition on the middle count | Proposed lower bound |
|---|---|---|
| \(012340\) | At most 2 | Outer sum at least 22 |
| \(012340\) | At most 3 | Outer sum at least 19 |
| \(012340\) | At most 5 | Outer sum at least 18 |
| \(012340\) | Unrestricted | Outer sum at least 17 |
| \(012034\) | Unrestricted | All five counts sum to at least 20 |
| \(012031\) | At most 5 | Outer sum at least 15 |
| \(012314\) | At most 2 | Outer sum at least 19 |

A four-count sum and a five-count sum overlap, so their extra charges
cannot be added using separate full budgets. Assign coefficient \(a\)
to each of the four outer positions and coefficient \(b\) to the middle
position, with

\[
4a+b\le120.
\]

Multiply an outer-sum shortfall in the clipped counts by \(a\). Multiply
a five-count shortfall by \(\min(a,b)\). Take the larger applicable
credit, after choosing the strongest valid bound within each category.
Its value is at most

\[
a\!\sum_{j\in\{4,5,7,8\}}
\bigl(\alpha_{r+j}-\min(6,\alpha_{r+j})\bigr)
+b\bigl(\alpha_{r+6}-\min(6,\alpha_{r+6})\bigr).
\]

Summing over suffix windows counts each of the four outer shifts once
and the middle shift once. The total added charge is therefore at most

\[
120\sum_{i=0}^{m}\bigl(\alpha_i-\min(6,\alpha_i)\bigr).
\]

Lean checks this argument for arbitrary nonnegative integer counts and
explicit local lower-bound hypotheses. It also checks that clipping
preserves the discarded-count contribution of 21. After multiplying by
120, the boundary contribution is 2,520. The existing share contribution
remains separate. Concrete selection of the direction-dependent lower
bounds and complete graph integration still require proof.

## Numerical improvement and its limit

The final experiment combines the seven rules with the previously proved
three-count restriction. It removes 33,362 further accepted keys beyond
that checked graph, leaving 4,909,227. This is 25,363 fewer keys than in
milestone 111's final hypothetical family.

| Profile | Minimum cycle mean | Recorded potential range | Exact comparison | Integer comparison |
|---|---:|---:|---:|---:|
| Completed local inputs | \(484\) | \(557\) | \(1103389/4684\) | \(235\) |
| Conditional local inputs | \(496\) | \(602\) | \(551765/2348\) | \(234\) |

These values use \((a,b)=(24,24)\). Every remaining edge satisfies its
saved integer potential inequality, and a saved cycle attains each
mean. The completed mean improves from milestone 111's \(3384/7\)
to \(484\). The integer comparisons do not change. These are conditional
finite-graph results, separate from complete Lean certificates for the
revised graph and its actual-snake interpretation.

The alternative allocation \((a,b)=(30,0)\), tested on the initial
six-rule family, gives completed mean \(1935/4\). This is weaker than
the balanced allocation. A coefficient screen can be stopped because
the final graph has a stronger obstruction: the completed profile has
a six-edge cycle with every count equal to 4 and edge weights

\[
480,\ 480,\ 492,\ 480,\ 480,\ 492.
\]

Every applicable deficit is zero, and the mean is exactly 484. The
conditional profile has a four-edge cycle with weights
\(498,612,498,376\), also with zero deficits, and mean 496. The deletion
rules are independent of the coefficients. Both cycles therefore survive
any nonnegative coefficient choice within this fixed family and retain
those weights. The balanced allocation attains both ceilings.

Even reducing the recorded potential ranges cannot improve the integer
comparisons while these mean ceilings remain. The relevant scaled
arithmetic is

\[
p\le484d
\quad\Longrightarrow\quad
(4200d+p)235\le1098960d+8p+R,
\]

and

\[
p\le496d
\quad\Longrightarrow\quad
(4200d+p)234\le1098960d+8p+R,
\]

for nonnegative integers \(p,d,R\). A graph mean uses \(d>0\).
Thus the present comparison still permits the indicated integer length.
Further improvement requires a stronger restriction or another source
of charge that changes these surviving cycles.

## Failed stronger claims and remaining work

Six selected local vertex sets have been independently checked. Their
count tuples include

\[
\begin{gathered}
(8,3,3,3,3),\quad(7,2,4,3,4),\quad(4,5,3,4,4),\\
(3,6,4,4,3),\quad(3,3,4,6,5),\quad(3,3,3,7,5).
\end{gathered}
\]

They prevent several stronger proposed inequalities in the current
local model. The sets have multiple components and relaxed boundary
conditions. They do not construct complete snakes or disprove claims
that use additional global information.

The test of outer sum at most 16 on \(012034\), with middle count at
most 4, remains unresolved after its bounded run. Proving the corresponding
lower bound 17 would affect the all-4 obstruction. A useful first test is
the exact all-4 tuple on that shape, followed by an attempt to recover
a family inequality if the tuple is impossible. Repeating coefficient
searches on the current seven rules cannot help.

The separate proof-generation attempt for \(012340\) with middle count
at most 5 and outer sum at most 17 timed out after 30 seconds. Its partial
proof is preserved as an unsuccessful attempt. The first export of the
successful \(012314\) certificate exceeded the checker's literal offset;
the later bijective renumbering resolves that representation issue.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit for 235, with the complete independent
rebuild pending. Conditional 234, the exact optimum and 196 remain
unresolved. The reference union still has 1,366 unresolved entries.
Milestone 104 continues the original potential batch. The paper remains
revision 106, with the next full revision scheduled for 116.
