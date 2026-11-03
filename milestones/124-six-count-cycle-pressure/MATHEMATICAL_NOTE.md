# Six-count bounds: coverage, a local proof, and direct length criteria

## Mathematical status

The maintained range remains $191\le a(9)\le235$, with the previously recorded
limitation on the independent rebuild of the upper bound. No improved
unconditional length bound is claimed in this round. The optimum and 196
remain unresolved.

The main new direction is to control six consecutive internal singleton-square
counts uniformly. The hypothesis is

$$
\sum_{j=0}^{5}\alpha_{r+j}\ge25
\qquad(1\le r,\ r+5<m).
$$

A universal lower bound of 25 would imply $m\le234$; replacing 25 by 26 would
imply $m\le233$. Lean checks both implications for actual snakes, including the
endpoint counts, positivity of internal counts and square budget used below.
Neither universal local hypothesis has been proved.

The manuscript notation $\alpha_i$, $b_i$, $\delta_i$, $T$ and $m$ is retained.
The arguments require no new mathematical definitions.

## Direct counting and a less restrictive sufficient condition

Take 38 disjoint groups of six internal positions. Their total is at least
$38L$ if every group has sum at least $L$. Every other internal count is at
least 1, and each endpoint count is at least 4. For $m\ge229$, this gives

$$
T\ge38L+(m-229)+8.
$$

With $L=26$, the square inequality $T+35(m+1)\le9214$ then gives
$36m+802\le9214$, which excludes $m\ge234$. With $L=25$, it gives
$36m+764\le9214$, excluding $m\ge235$. These are conditional consequences of
the stated local floors. The endpoint, positivity and square hypotheses have
been discharged for actual snakes.

A sharper criterion for excluding 235 uses 39 disjoint groups, covering
internal positions 1 through 234. The exact sufficient condition is

$$
\sum_{b=0}^{38}\max\left\{0,
25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}\le28.
$$

Indeed, when $m\ge235$, the first 234 internal counts total at least $975-28$;
the other internal positions contribute at least $m-235$, and the endpoints
contribute at least 8. Thus $T\ge m+720$, and the square inequality gives
$36m+755\le9214$. At $m=235$, the left side is 9215, a contradiction.

It suffices that every one of these 39 group sums is at least 23 and at most 14
are below 25: their combined shortfall is at most $2\cdot14=28$. The stronger
assumption of at most 13 such groups gives shortfall at most 26. No result here
identifies these deficient groups with the endpoint-related occurrences from
milestone 122. That geometric connection, and the lower floor 23, remain
separate hypotheses.

## Exhaustive direction coverage and native evidence

Independent enumeration gives 34 induced restricted-growth direction words
of length 7, among 877 unrestricted words of this form. Identifying reversal
leaves 21 classes: eight self-reverse words and thirteen pairs. All 21 classes
occur in the saved bank of 134 paths. The smallest observed six-count sum is 31;
this finite-bank minimum is not asserted to be universal.

The full-cube screen and its bounded resumes leave 19 native-negative classes
and two unresolved classes, $0120310$ and $0120324$. The ordinary tests search
for six-count sum at most 24; the reused $0123042$ case has the stronger cap 25.
There are no saved path counterexamples. Three smaller-radius controls remain
unresolved and do not affect the full-cube coverage count.

The independent probe audit reconstructs 29 records, including the pinned prior
result. Every sum preserves 126 corner occurrences, with 100–106 distinct
vertices and repetitions up to three. It verifies 120 cut records, representing
81 distinct vertex sets. A selected set with minimum internal degree at least
two contains a cycle and cannot lie inside an induced path; all saved cuts
satisfy that check. Last cyclic-model censuses are not path witnesses.

A negative solver status alone is insufficient. One of the 19 negative classes,
$0123041$, now has a checked contradiction certificate, count-sum semantics and
transfer to actual snakes. Eighteen other negative classes require these proof
steps, and the two unresolved classes still require a decisive result. The
earlier 34-case exact-four proof does not imply a sum floor.
Historical normalization sources and logs were audited, but some old
source/object hash pairings are absent and must be refreshed before claiming
a newly closed universal coverage proof.

## One selected local certificate

The selected case is $0123041$, whose canonical window is
$(0,1,3,7,15,14,30,28)$. Its six internal counts lie in $[0,21]$ and are assumed,
for contradiction, to sum to at most 24. The complete formula has 101,898 clauses
and 5,072 variables; it requires no added cycle cuts.

The trimmed certificate has 3,649 original inputs, 5,746 deductions and 439,766
propagation hints. Independent replay verifies the final contradiction. The
counter has 126 occurrences across 105 vertices: 85 occur once, 19 twice and one
three times. The source audit confirms that all repetitions are preserved.
Forty isolated Lean modules represent the concrete semantics and contradiction.
The actual-snake wrapper uses the checked coordinate normalization and count
transfer; a separate reversal theorem covers either orientation.

All forty certificate modules and the actual-snake and reversal arguments
have passed Lean. The resulting checked conclusion is

$$
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}
+\alpha_{r+4}+\alpha_{r+5}+\alpha_{r+6}\ge25
$$

whenever the seven-transition segment has canonical shape $0123041$, in either
orientation. This one-class conclusion leaves the universal statement unresolved.

The full round contains 46 checked modules and 22 printed dependency reports.
The reports use only the standard dependencies `propext`, `Classical.choice`
and `Quot.sound`. The independent receipt review checks the exact sources,
compiled objects, logs, dependency files and resolved imports. The initial
semantic compile timed out; its preserved log is separate from the successful
retry. Both export processes recorded errors, although the second produced the
complete output. The archived outputs, final published files and Lean receipts
are checked independently; neither export process is described as successful.

## Why the three-pattern graph route was insufficient

The combined graph test grants floors 26, 25, 25 on $0123042$, $0120310$ and
$0123024$. It preserves the existing coefficient 24 under the exact-first-count
guard, takes the maximum of overlapping credits, and preserves the full
$[6,21]$ meaning of symbol 6. It removes 10,082 additional keys and increases
credit on 41,762 retained keys.

Nevertheless, both original attaining cycles survive because they avoid all
three shapes. Checking every retained-edge inequality gives the same means,
$2915/6$ and 496, and the same integer comparisons 235 and 234. Any further
increase of those three floors leaves these cycles unchanged. Even setting
the potential range to zero cannot improve those integer comparisons.

The conditional cycle's windows all belong, after reversal, to $0120324$ and
have exact sums 22, 24 or 26. The completed cycle also involves $0120340$,
$0120342$, $0123014$ and $0123104$. These surviving cases explain why uniform
coverage or a proved bound on total shortfall is more useful than repeatedly
strengthening only the original three patterns.

## Continuation and evidence

The next mathematical priority is to resolve $0120310$ and $0120324$, or find
an actual counterexample to the universal 25 hypothesis. A second precise
route within the same counting argument is to prove the shortfall bound 28;
no endpoint interpretation for that bound is assumed. Certificates for the
other negative classes can be checked independently, with exact provenance.

Read `audit/probe-review.md`, `audit/coverage-review.md`,
`audit/certificate-review.md`, `audit/graph-review.md`, and the final
`audit/proof-review.md` for the distinct scopes. The source-stage derivation
notes record when their files were first written; the final receipts determine
what was actually compiled. A timeout is retained as an incomplete attempt,
never a contradiction or a failed theorem.

The older 104, 115 and 122 verification batches remain separate. Their progress
must be checked against live processes before resuming anything. Paper revision
116 is unchanged; the next full manuscript revision remains 126.
