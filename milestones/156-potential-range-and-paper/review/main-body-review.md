# Main-body review for revision 156

Reviewed source: `E:/Snake-in-a-box/paper/snake9_research.tex`.

Exact full-source SHA-256:
`b3b06d3df379436f81b59d723d80bd01902d566e6d0617ceb860b155e4186e80`.

The entire source from line 1 through line 3139 was read in contiguous
chunks; line 3140 begins the appendix. This includes the preamble, abstract,
every main-body section, and every proof in those sections. The review did
not rely only on search hits. No paper, execution source, or proof artifact
was edited. No compiler, solver, or graph calculation was run for this review.
This is a logical and editorial review, not a new audit of every historical
certificate or a visual review of the compiled PDF.

## Coverage

| Lines | Section | Principal assessment |
|---|---|---|
| 1--65 | Preamble and abstract | Preserve all authors, title metadata, hyperref settings and existing packages. Abstract states completed16/17 correctly but gives disproportionate space to an obsolete fixed-profile cycle obstruction. |
| 66--145 | Problem, notation, and principal result | Definitions and edge/vertex convention are clear. The evidence table should distinguish actual-state construction from conditional reference retention, and should mention completed share17. |
| 146--225 | Exact square census | The incidence deduction, positivity and endpoint proofs have a coherent order. Retain the nontrivial-path qualifications and the distinction between internal and endpoint count ranges. |
| 226--303 | Upper bound235 and retained empty squares | The contributor proof and pending independent rebuild are distinguished. Keep the boundary calculation and the eighteen-empty-square consequence. |
| 304--419 | Direct six-count bounds | Conditional universal hypotheses are explicit; the single proved0123041 class is correctly distinguished from them. Keep the shortfall statement and its exact group count. |
| 420--475 | Distance-three pair restrictions | Direct geometric proofs and sharpness witnesses are separated clearly. |
| 476--576 | Outer pair and endpoint obstruction | The full eight-transition condition, Hamming distance and overlap capacity are essential and explicit. |
| 577--1255 | Integer shares, then count and endpoint restrictions | The share definition and packing argument are well placed. The long count-only sequence beginning at725 interrupts the share exposition and should be grouped with the local count results. |
| 1256--1357 | Geometric empty-square bounds | Monotonicity, forced absence, exhaustive alternatives and saturation form a clear dependency chain. No new terminology is needed. |
| 1358--1403 | Longer-segment count restrictions | Complete statements are readable; distinguish their valid local exclusions from any claim that all low-charge cycles disappear. |
| 1404--1646 | Compatibility and excess | The count correction and common-budget cautions are important. Historical diagnostic discussion can be shortened; repeated definitions of the same truncated count/excess can be references. |
| 1647--1710 | Count-free share catalogue | Current universal01203216 status is correct. Rename the section to include its existing count-conditioned120 theorem and relocate completed17 here. |
| 1711--1851 | Common budgets | The maximum rule, offset capacities and separate count/share budgets are explicit. Preserve these when shortening surrounding prose. |
| 1852--1929 | Window and boundary accounting | The number of transitions, omitted vertices, empty-window case and strict235 exclusion criterion are stated coherently. |
| 1930--2576 | Baseline graph and interpretation | The full-key and history details are necessary. Several numerical-profile names and five-unfinished-share statements are stale. The archival baseline012032 floor0 must remain attached to its original weights and certificates. |
| 2577--2678 | Further proved count restrictions | All three results are stated independently of later graph hypotheses. Move them into the local-count group without changing statements or proofs. |
| 2679--2909 | Retained-graph limitations | Exact fixed-profile qualifiers are essential. The original-source graph obstruction at2857 belongs with the original graph, not inside the retained-graph section. |
| 2910--2965 | Remaining requirements | Four pending local floors are correctly listed. Separate original-graph certificate completion from the additional premises of a retained-graph refinement. Update the open range discussion. |
| 2966--3139 | Verification and remaining problem | Completed16/17 and conditional012301 are correctly distinguished. The share17 theorem and mathematical graph effect are misplaced inside verification history; move them to the catalogue and graph section respectively. |

## Required correction: keep mathematical profiles distinct from current proof status

At lines2293--2312 the text calls two numerical vectors the “current” floor
choices and labels a column “Completed floor”, while its012032 entry is0.
At lines2411--2422 the range551/mean483 profile is described as using all
bounds in the updated count-independent theorem, which now includes
01203216. These descriptions cannot both identify the same stored weights.

Do not change the archived0 entry to16 while retaining its historical weight
hash, attaining cycle and exact minimum mean. Increasing a floor preserves
feasibility of a potential, but need not preserve which cycle attains its
mean. Preserve the original numerical profile and correct its name.

Replace the text ending “The two current floor choices are:” at2292--2293 by:

```tex
the share-120 rule, and the chosen count-independent floor. The following
two archived floor profiles specify the numerical certificates discussed
in this section. The baseline retains its original zero entry for $012032$;
the stronger universal floor 16 is now proved separately.
```

Replace the table heading at2297 by:

```tex
Six-transition shape & Archived baseline floor & Conditional floor\\\midrule
```

Replace2309--2312 by:

```tex
A zero entry contributes no count-independent estimate in that archived
profile. All other applicable bounds remain in the maximum. The conditional
profile uses floors $(16,18,16,16,16)$ for
$012032,012034,012301,012340,012345$. The first is established by
Theorem~\ref{thm:countfree-completed}; the other four remain unresolved.
```

Theorems and corollaries retaining five mathematical premises remain valid:
one premise is now available from a proved theorem. Do not mechanically
change an archived checked theorem's interface or claim that a new composed
Lean theorem was checked. In explanatory prose, distinguish **five entries
in the conditional vector** from **four outstanding local proofs**.

Replace the second comparison-table row's label at2411 by:

```tex
Archived baseline shares, without the universal $012032$ floor
```

Replace the third row's label at2412 by:

```tex
Archived baseline and the proposed $012034$ floor 20
```

Replace2418--2423, up to “Separate integer computations”, by:

```tex
The first three rows retain their original numerical profiles. The second
uses the archived baseline shares and gives integer bound 235 under the
reference and potential premises; its weights do not include the later
universal $012032$ floor. The third adds the unproved $012034$ floor 20
and still gives235. The fourth and fifth use the five target entries,
of which four local theorems remain unresolved. The last row reduces the
$012034$ target to18 and has strict margin30 at length235.
```

Use “archived baseline” consistently at2315,2357,2369,2401 and2937.
The numerical values and labels should remain unchanged. References to
“five local share premises” at2324,2358 and2370 can remain with the preceding
clarification, or say “the listed local share premises, of which the012032
case is now established”.

## Required correction: state which graph a limitation concerns

The heading “Current limitations of the retained graph” contains a later
subsection explicitly returning to the original4,947,008-row graph.
This makes reuse of the old three-cycle particularly easy to misunderstand.
Move the entire subsection2857--2908, including its label, proposition,
proof and citation, to the original-graph section immediately after
`sec:least-floors`. Its mathematics is unchanged.

The retained-graph discussion should identify its archived profile before
the first numerical comparison. Replace2680--2684 by:

```tex
This section fixes the retained graph of4661572 transitions and the
archived weights specified in each proposition.
Appendix~\ref{sec:sum-refinements} records the additional count hypotheses
used to construct that graph. Its cycle witnesses need not be realizable
by complete snakes. The baseline comparisons below precede the installation
of the universal $012032$ floor16; changes to that floor are stated explicitly.
```

Replace2846--2851 by:

```tex
The proved universal $012032$ floor16 changes the eleven-cycle: it adds57
to its total, giving mean496 at zero occurrence credit. Together with the
still-unproved floors16 for $012301$ and $012340$, it gives mean496 on
both saved cycles. The count-conditioned floor17 in
Theorem~\ref{thm:critical-count-share17} increases two eleven-cycle edges
by one further unit and leaves the fourteen-cycle unchanged. These local
changes require their own complete edge and range checks.
```

The last sentence should be updated to cite the accepted156 numerical
certificate once that certificate is included in the revised paper. The
additional local premises and missing actual-snake assembly remain.

## Completed share17 belongs in the local share catalogue

Move3067--3106 intact to the share catalogue, preferably after
Theorem`thm:share120` and before the target table. Preserve the theorem
label, both count orders, the fitting condition and the proof citations.
The reverse tuple must remain
\((3,\le5,4,\le4,4)\) in the original path order. The theorem is not a
universal share17 floor and carries no remaining contradiction premise.

Rename section1647, preserving its label, to:

```tex
\section{A catalogue of five-centre share bounds}\label{sec:countfree-catalogue}
```

Its current title already excludes its own count-conditioned120 theorem;
the broader title describes the actual contents without adding a definition.
After the moved theorem, extend the maximum-rule paragraph at1708 to name
all applicable count-independent, share120 and count-conditioned17 bounds.
Each alternative concerns the same five centres and enters a maximum.

The repeated counter-removal narrative and the earlier exact tuple at
3042--3065 can become a concise verification paragraph:

```tex
The count-conditioned share theorem
\ref{thm:critical-count-share17} uses the same11869-clause compact core
for its exact and broader count interpretations. Its98 interpretation
and transfer modules,137 complete replay modules, and final actual-snake
composition have passed Lean. The replay contains30305 deductions and
1754767 propagation references. The count conditions remain in the final
statement, while the contradiction premise has been discharged
~\cite{critical153archive,broader154archive,share155archive}.
```

Move3108--3121, which concerns retained rows and cycle weights, to the graph
discussion. Preserve the distinction between100 extra source rows across
both placements and the suffix rows actually receiving a contribution.
Broadening adds no retained match under the inherited pair-floor9 condition.

## Clarify the two proof packages behind reference-catalogue statements

The proof of235 uses the completed contributor theorem at261--264. Later,
the independent share package retains1,358 exact-system refutations as
premises. These statements can coexist, but readers need the distinction
at the first appearance of the reference-union premise. Add after2122:

```tex
The contributor theorem used for235 and the present exact-reference proof
package are separate dependencies. The propositions below retain
refutations of these particular local systems as hypotheses. Reusing an
archived result to discharge those hypotheses requires a checked transfer
to this interface. The count of outstanding entries refers to this package.
```

Do not assert that contributor proofs are missing merely because the newer
package has pending dependencies. Conversely, do not declare its reference
premise discharged solely by identifying overlapping direction/count keys.

The evidence-table row128 should say:

```tex
Actual-state construction and weight accounting & State construction,
non-reference filters and baseline weights are checked. Reference retention
is conditional on the remaining1358 entries of the1378-key union.\\
```

Add one concise row for the universal16 and count-conditioned17 conclusions,
referring to their theorem labels rather than repeating module counts.

## Range status and the new156 result

Lines2510--2512 say that optimality of range602 has not been established.
That sentence describes the earlier computation and is no longer a suitable
unqualified current-status statement. The saved original-source rows now
give a28-edge walk of weight13286, forcing range602 at mean496; its
three-cycle still caps the mean at496. Neither has a share17 match.
Together with the old all-edge potential this determines the best comparison
for that original fixed profile. This saved-row arithmetic is distinct from
the new retained-graph certificate.

Suggested replacement for2510--2514:

```tex
The saved potential has range602 at mean496. On this original graph, the
saved28-edge walk has weight13286 under the sufficient floor profile,
so every potential at that mean has range at least602. The range is
therefore minimal at this mean for these fixed weights. Changes to graph
restrictions, boundary estimates or credits require a separate comparison.
```

The full original-profile optimum additionally uses its own three-cycle
and its denominator calculation. Do not substitute that three-cycle into
the retained graph, which removes two of its edges.

After the full main-body reading, the coordinating agent reported the
accepted156 result: the retained-profile optimum is also range602, now
certified by a surviving nine-edge walk of total3862 and the fourteen-cycle
of total6944. The reported Lean arithmetic gives
\(\mu\le496\), \(R\ge9\mu-3862\), and comparison at least
\(551765/2348=235-15/2348\) for nonnegative mean and uniform credit,
with equality forcing mean496, zero credit and range602. The new all-edge
scan attains this value. This review does not duplicate that numerical or
Lean audit; its final publication should cite the coordinating agent's
accepted156 records.

Include that result as a separate, explicitly fixed-profile proposition
in the retained-graph section. Retain the full vector, the144 removals,
the maximum rule, the additional count/six-floor assumptions, and the
occurrence allowance24. It refutes the selected improvement R<602 and
settles that comparison's mean/range/uniform-credit optimization. It does
not close the four local floors, reference or graph-to-snake obligations,
and it gives no new global upper bound. Update2947--2959 to distinguish
this completed finite comparison from the remaining proof obligations.

## Recommended reordering and shortening

Preserve every accepted mathematical statement, existing label and citation.
The useful changes concern placement and scope:

1. Keep the square census, archived235 proof and direct conditional targets
   near the beginning.
2. Group the count-only subsections725--1254 with the pair and endpoint
   results. Move2577--2678 into that group. They require the singleton-count
   machinery, not the share definition. Keep their internal dependency order.
3. Present the share definition and packing, geometric bounds, catalogue
   including completed17, and common budgets as a continuous sequence.
4. Keep compatibility/excess theorems after the share definition, since their
   corollaries use the charge. Their long historical diagnostic remarks can
   be reduced to links to the existing diagnostic appendix.
5. Separate the original accepted-key graph and its fixed-profile comparisons
   from the later retained graph. Put the new156 proposition with the latter.
6. End with the unresolved actual-snake obligations and a short verification
   summary. Move implementation history and duplicate certificate counts to
   the existing historical-verification appendix, retaining citations.

For the abstract, replace the detailed obsolete two-cycle restriction at
52--56 by a short current statement about completed local shares and the
scoped finite-comparison limitation. If including156, distinguish its
optimal fixed comparison from the unresolved snake optimum. Avoid suggesting
that the old unchanged-eleven-cycle inequality still constrains the new
weights. Keep the main interval and the pending independent rebuild.

## Definitions and non-negotiable scope

There is only one `definition` environment in the reviewed main body, the
snake itself. The problem is repeated notation and dispersed results,
rather than an excessive number of definition environments. Retain the
recurring singleton counts, clipped counts/excess, shares, total charge,
history signature and potential notation. No new named definition is needed.
At1472--1475,1575 and1628, a short reference to the already defined clipped
count and excess can replace a repeated definition, while leaving all
indices and local hypotheses intact.

Preserve the following distinctions during rewriting:

- Length counts edges; empty-square counts refer to distinct squares.
- Only internal count6 denotes the interval[6,21]; endpoint counts are not
  assigned that internal upper bound.
- Reversal reverses the count tuple as well as the transition sequence.
- A share maximum gives alternative bounds on one sum; adding overlapping
  bounds requires the explicit common capacity.
- Interior degree lower bounds require all neighbours to be represented.
- Local models and finite graph cycles need not be complete snakes.
- A numerical all-edge certificate and checked arithmetic do not by
  themselves constitute the missing full graph-to-snake Lean composition.
- The contributor235 proof and its independent rebuild are different
  verification claims. The conjectured value196 is used in none of the
  proved bounds.

No mathematical statement was disproved by this reading. The highest-priority
corrections are profile identity, current versus historical proof status,
the location of the completed17 theorem, and explicit scope for the new
fixed-profile range result.
