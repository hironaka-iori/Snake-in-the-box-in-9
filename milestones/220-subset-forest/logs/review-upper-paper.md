# Round 220: review of the upper-bound portion of the manuscript

Reviewed source: `data/before-snake9_research.tex`.

SHA-256: `9bd201b7b4fff3a344c7785d0c36c05b4495fef386004274aaf8a7aa4b0120ba`.

## Coverage and limits

Every line from 1 through 4139 was read, in the following untruncated chunks: 1–400, 401–800, 801–1200, 1201–1600, 1601–2000, 2001–2400, 2401–2800, 2801–3200, 3201–3600, 3601–4000, and 4001–4139. This covers the preamble and abstract, the complete upper-bound argument and its alternative comparisons, and the initial numerical-conjecture discussion. No later manuscript lines are included in this review.

This is a textual and mathematical source review. No proof artifacts were rebuilt, no local certificate or full graph was replayed, and no solver, compiler, search worker, or software tests were run. The saved contributor-status review from round 213 and the exact fractional-certificate audit from round 219 were consulted for the two decisive status claims. This does not independently repeat either earlier audit.

## Corrections to make

### 1. The historical 235 proof incorrectly claims the principal 233 theorem

**Lines 369–371, proof of Theorem `thm:upper235`.** After obtaining only the upper bound 235, the text says that this and the lower construction prove Theorem `thm:main`. The principal theorem at lines 117–128 now states the interval ending at 233. The cited argument cannot establish that stronger interval.

Replace the closing sentences by:

> The zero-edge path satisfies the length bound directly. This completes the archived upper bound 235. The stronger upper bound in Theorem~\ref{thm:main} is supplied by the separate contributor argument in Section~\ref{sec:bound233}.

This is a proof-reference error; it does not identify a defect in the separate 233 deduction at lines 3902–3935.

### 2. Three historical statements still read as current global status

The section introductions correctly preserve historical constants, but these sentences should also make their scope explicit:

- **Lines 382–384:** “the numerical length upper bound remains 235.” Replace with “the numerical conclusion of this archived count-only argument remains 235.”
- **Lines 901–905:** after describing unresolved share and graph premises, “consequently this does not exclude a 235-edge snake unconditionally.” A completed 233 theorem has already been stated. Replace the final sentence by “The local share and graph premises remain unresolved, so this alternative argument does not independently supply that exclusion.”
- **Lines 3459–3461:** “Together with the maintained upper bound 235” is stale. Replace with “In this earlier argument, the archived upper bound 235 reduced the task to excluding length 235. Its odd parity supplies this particular graph premise; the other premises remain explicit.”

Do not replace the historical numerical constants or weaken the distinction between the completed contributor route and the incomplete alternative packages.

### 3. The scaled rounding calculation reuses the selected-set symbol without explanation

**Lines 3695–3696:** `A=2520S+B` introduces three scalar symbols without identifying them. In particular, \(S\) already denotes the selected vertex set, so this display reads as an operation on a set.

The preceding argument already supplies the needed quantities. A direct replacement avoiding new symbols is:

> After multiplication by 2520, the rational share must exceed 36288 and the rounding deficit is at most 1008. The scaled integer share therefore exceeds \(36288-1008=35280=2520\cdot14\), so the integer share is at least fifteen. These arithmetic implications pass Lean.

This preserves the strict inequality and the fact that equality at \(72/5\) does not suffice.

### 4. Name the archived baseline consistently in the actual-weight theorem

**Lines 2687–2709, 2712, and 2757.** The table deliberately gives the archived baseline floor zero at `012032`, although the stronger universal floor sixteen is now proved. The theorem and corollary then call this choice “the completed floor choice” or “completed floors.” The mathematics is valid for the weaker profile, but the label can suggest that the later floor sixteen has been installed in the reported graph weights.

Use “the archived baseline floor choice” at lines 2712 and 2757, and retain the explicit zero-versus-sixteen explanation. At lines 2722–2723 and 2770–2771, “the five stated local bounds, four of which remain unresolved” would make the proof status clearer without changing the assumptions.

### 5. Express the retained-graph pair condition using its stored counts

**Lines 3324–3330.** The argument concerns rows of a finite graph, but describes its requirement directly as an inequality between actual \(\alpha\) counts. The graph stores truncated symbols and its pair-floor applicability is itself conditional, as correctly stated at lines 3354–3358.

State that the retained rows require the two stored symbols to sum to at least nine. The tested caps are at most four and five, so both symbols are unsaturated and must equal four and five. For an actual snake tracing such a row, the same equalities then hold for the actual counts. Keep the final qualification about the graph's removal hypotheses. This avoids presenting its pair-nine restriction as universal for all snakes or all window parities.

## Arguments that read consistently

- The abstract and principal theorem distinguish the completed contributor theorem from a pending independent rebuild. Section `sec:bound233` retains the external-object, incremental-audit and source-regeneration limitations. The round-213 pinned review supports this distinction; the alternative reference/certificate packages are explicitly kept separate.
- The exact square census has the correct incidence counts and uses the internal-vertex correspondence to obtain \(s_3=v-2\). Its nontrivial-path assumption is stated.
- The written positivity and endpoint-four proofs identify the endpoint-count contradiction explicitly. The six- and seven-count boundary deductions correctly use the stronger adjacent-one and forbidden-three-twos restrictions. Their sharp numerical tuples are correctly distinguished from realized snake tuples.
- The missing-pair component proof uses connectivity of the actual path, rather than degree conditions alone, to infer closure of the entire selected set. The exact disconnected lengths are distinguished from the narrower checked lower-bound consequence.
- The endpoint occurrence argument retains the common-unselected-neighbour hypothesis. The count-twelve proof constructs blocks, budgets their overlaps, excludes the two exceptional sampled positions, and treats the exceptional parameter case separately. It does not incorrectly apply the both-endpoint count-thirteen theorem to a single-endpoint assignment.
- The share arguments use maxima for alternative lower bounds on the same centres and keep multiplicity budgets explicit. Saturated count symbol six is consistently distinguished from exact count six in the filter and excess arguments.
- The history automaton discussion separates recognition of canonical identifiers from coverage of all compatible coordinate words. The actual-state argument keeps full edge keys, avoiding identification of parallel rows solely by endpoints.
- The retained-graph mean/range obstructions retain their graph, floor, boundary and occurrence-credit assumptions. They are described as restrictions on specified finite comparisons, with no claim that their cycles are actual snakes.
- The model extrapolation to 196 is explicitly separated from proof, and the alternative interpolation predicting 195 correctly demonstrates the insufficiency of the observed terms.

## Arithmetic spot checks

These displayed deductions were checked directly during reading; this is not a fresh verification of the certificates supplying their premises.

1. \(T\ge4m-13\) and the square census give \(39m+2s_0\le9192\). At \(m=235\), the allowance for \(2s_0\) is 27.
2. The boundary-24 packing and exact share budget give \(W+4200m+5L\le1098600\).
3. With \(9\mu=4454\) and \(9R=5421\), that budget gives \(42254m+45L\le9928453\). The margin at 235 is 1237.
4. The original B233 inequalities \(520(m-7)\le W+1023\) and \(W+4200m\le1099800\) give \(4720m\le1104463\), which excludes 234 by 17.
5. The four-unit allowance in the separate relaxed argument gives \(4716m+5L\le1103475\), excluding 234 by 69 when \(L\ge0\).

No contrary arithmetic or missing hypothesis was found in these displayed deductions. This statement does not certify every numerical table, certificate size, catalogue count or finite enumeration appearing in the reviewed range.

## Status cross-checks

Read `milestones/213-interval-geometry/logs/contributor233-review.md`: it records the exact upper theorem at pinned contributor revision `b0521e1d14fd52c62db4cdeccc356b70a623eb82`, its saved final audit at `b65d30ca15441420b8f4538f671e589c2502674f`, and the independent-rebuild limitation. These agree with the manuscript's abbreviated references and stated scope.

Read the status and scope of `milestones/219-linear-partner/data/rational-audit.json`: its exact fractional points, including cardinality 94 and all simple-cycle occupancy inequalities, support the abstract's round-219 limitation. They do not support Boolean feasibility or an improved global bound, and the abstract makes neither claim.

The manuscript was not edited. The priority correction is the false proof reference in the historical 235 theorem; the remaining proposals clarify status and notation while preserving the mathematical arguments and historical evidence.
