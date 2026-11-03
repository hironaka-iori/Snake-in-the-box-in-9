# Six-count restrictions with the empty-square term retained

The new results strengthen the conditional length criteria and restrict a
possible counterexample on direction pattern $0120324$. They do not establish
a new unconditional length bound. The maintained range remains
$191\le a(9)\le235$, with the previously recorded independent-rebuild
limitation on the upper bound. The optimum and 196 remain unresolved.

The existing notation $\alpha_i$, $T$, $s_0$ and $m$ is sufficient throughout.
Here $m$ is the number of edges and $s_0$ is the number of empty squares.

## Retaining empty squares

The square-incidence argument gives

$$
T+35(m+1)+2s_0\le9214.
$$

If $m\ge235$, partition the first 234 internal positions into 39 groups of six.
Their total, plus their combined shortfall below 25, is at least $39\cdot25$.
Each of the remaining $m-235$ internal counts contributes at least one, and
the endpoints contribute at least eight. Consequently

$$
T+\sum_{b=0}^{38}\max\left\{0,
25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}\ge m+748.
$$

Combining these inequalities shows that every snake with $m\ge235$ satisfies

$$
\sum_{b=0}^{38}\max\left\{0,
25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}
\ge29+2s_0.
$$

This is a necessary condition for actual snakes, checked in Lean. Thus proving
that the same sum is at most $28+2s_0$ would imply $m\le234$. The earlier
criterion discarded the empty-square term and required the sum to be at most
28. No upper bound on the shortfall or lower bound on $s_0$ is inferred here.

The same counting argument gives the following checked implications.
Every six-count assumption refers to all fitting groups of six consecutive
internal counts. The empty-square assumption need only hold for the lengths
being excluded.

| Six-count lower bound | Additional empty-square assumption | Consequence |
| --- | --- | --- |
| 25 | None | $m\le234$ |
| 24 | $s_0\ge6$ when $m\ge235$ | $m\le234$ |
| 23 | $s_0\ge25$ when $m\ge235$ | $m\le234$ |
| 25 | $s_0\ge14$ when $m\ge234$ | $m\le233$ |

For the middle two rows, 39 disjoint groups give respectively
$T\ge m+709$ and $T\ge m+670$. At $m=235$, adding the square term and the stated
empty-square contribution gives 9216 and 9215, exceeding 9214.
For the last row, 38 groups give $T\ge m+729$; at $m\ge234$, the square budget
forces $s_0\le13$. The displayed additional assumption therefore excludes
these lengths.

All universal six-count and additional empty-square assumptions in this table
remain unproved. These are precise sufficient conditions, not improved
unconditional bounds. The implementation counts each empty square at its four
corners; the actual-snake statements retain that exact factor of four.

## A restriction on the unresolved direction pattern

Suppose a seven-transition segment beginning at $r$ has canonical word
$0120324$, with $r+7\le m$. Its prefix has word $012032$, and its suffix has
canonical word $012314$. Existing checked results give

$$
\alpha_{r+2},\alpha_{r+4}\ge2.
$$

If $\alpha_{r+4}=2$, a prefix exclusion forces $\alpha_{r+1}\ge3$.
The suffix theorem then gives

$$
\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge19.
$$

The six-count total is therefore at least $3+2+19=24$. A counterexample to
the proposed floor 23 must instead have $\alpha_{r+4}\ge3$. Together with
positivity and the known internal upper bound, every matching actual window
whose total is at most 22 lies in the intervals

$$
([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).
$$

Lean checks the canonical prefix and suffix, the transfer of the saved
exclusion, and this complete interval restriction. This is a necessary
condition for a counterexample; it does not exclude all such counterexamples.

A separate review shows why simply adding the currently selected pair and
five-count inequalities is insufficient. Those inequalities and the reviewed
triple exclusion imply a floor of 18, but the abstract tuple
$(2,4,3,4,2,3)$ satisfies them and has total 18. This tuple is not asserted to
occur in a snake. It only shows that the explicitly reviewed inequalities
cannot alone imply 23 or 25. The review does not exhaust the historical
exclusion catalogue.

## Search evidence and limitations

All searches use the full 512-vertex cube. Permuting the four coordinates unused
by $0120324$ produces 35 distinct cycle exclusions from the eight saved seeds.
Each exclusion is checked as a connected induced cycle. All 126 corner
occurrences are retained, including repetitions over the 100 distinct corners.

| Search | Variables | Clauses | Result |
| --- | ---: | ---: | --- |
| Six-count total at most 24 | 5,072 | 101,933 | Timeout after 120.062 seconds |
| Six-count total at most 22 | 4,820 | 101,431 | Timeout after 60.172 seconds |
| Total at most 22 with the checked interval restriction | 7,277 | 106,348 | Timeout after 60.062 seconds |

No run returned a complete model or a contradiction. Partial proof traces do
not prove impossibility. The formula audits independently reconstruct the
clauses, cycle exclusions and counter multiplicities. Their historical records
remain unchanged, including the bounded-search audit made before the successful
actual-snake interval proof.

Three Lean modules contain 19 printed dependency reports. The first interval
proof attempt failed on a namespace reference and unreduced index expressions;
its source and log are preserved. The repaired source passed. The independent
main review and supplement record the exact scope and dependencies.

## Next step and preservation

The strongest next encoding change is to append 235 direct cardinality clauses
that express the six existing lower bounds. Each must first be derived by
checked unit propagation from the original 106,348-clause formula. Concatenating
these derivations with a subsequent solver trace can preserve the original
semantic proof. Trimming and replay must use the original formula as input,
so the added clauses remain derived statements. This proposal has been reviewed
but has not been implemented or tested. See `data/next-encoding-task.json`.

Every partial trace is retained locally and has a lossless gzip archive for
the repository. The checkpoint manifest excludes only the three redundant
uncompressed copies. Their hashes and restoration paths are recorded in
`data/partial-proof-archive.json` and `data/partial-proof-archives-extra.json`.
Restore them before running the search auditors on a fresh checkout. Archive
integrity is separate from mathematical proof.

The older 104, 115 and 122 proof batches remain separate. Inspect live processes
before resuming them. Paper revision 116 is unchanged; the next full revision
is due at milestone 126 and should incorporate this round's distinctions.
