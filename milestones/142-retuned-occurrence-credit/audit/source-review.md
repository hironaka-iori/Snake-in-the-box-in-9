# Retuned-credit source review

Status: **PASS_SOURCE_REVIEW_RESULT_AVAILABLE**. The complete derivation from milestone141's frozen evaluator was inspected. No source correction is needed. The separate bounded result review also passed; its scope and findings are in `audit/result-review.md` and `data/result-review.json`. No graph, solver, Lean compiler, or large array was run or loaded during the source-review stage.

The new calculation evaluates the completed profile only, using integer weights

\[
W_e=12w_e+533\mathbf 1_e.
\]

Here the unchanged suffix-event indicator still requires shape `012032`, both pair-count symbols below 6, and pair sum at most 9. The exclusion masks and existing shared maximum are unchanged. The additional-share profile remains the separate milestone141 zero-credit result: mean 496, range 602, and comparison \(551765/2348\). Its whole result file is pinned through the new predecessor reconstruction.

The historical milestone139 reconstruction correctly retains multiplier 3 and credit 83 in its integer expression. Both remaining `83*event` expressions are historical: the old weight-hash check and the old four-cycle comparison. They are unchanged. The new milestone141 reconstruction separately compares its removal set, edge count, and both original zero-credit weight hashes before any retuned weights are evaluated.

The weak-exclusion proof gate remains pointed at milestone140's checked completion record. Its actual theorem source and successful audit receipt hashes agree with the completion record. The proof gate executes before graph imports. No proof replay was performed here.

For a certified scaled mean \(p/d\) and integer potential range \(R\), the original mean and range are

\[
\mu=\frac p{12d},\qquad \rho=\frac R{12d}.
\]

The evaluator correctly uses

\[
B=\frac{12\cdot1098960d+8p+24\cdot533d+R}{12\cdot4200d+p},
\qquad
B-235=\frac{R+1356312d-227p}{50400d+p}.
\]

At the target original mean \(3011/6\), the reduced scaled mean is 6022. Thus \(p=6022,d=1\), and

\[
B-235=\frac{R-10682}{56422}.
\]

The strict condition is \(R<10682\), equivalently \(\rho<5341/6\). Equality gives 235. The saved seven-cycle calculation also checks exactly:

\[
\frac{3424+2(533/12)}7=\frac{3011}{6}.
\]

This selects a candidate credit by equalizing two saved cycle comparisons. It does not establish the new minimum, optimal credit, or optimal potential range. The actual run computes its own minimum and range before evaluating the comparison.

Output means, ranges, scaled occurrence credits, zero-range comparisons, and target flags consistently use multiplier 12. The full-edge potential check, attaining-cycle check, integer overflow guard, source rechecks, resource gate, and failure records remain in place. The review found no conversion of a historical profile to the new units.

Six rational arithmetic cases, including both sides of the strict range threshold and equality, passed. Exact source pins and the arithmetic results are recorded in `data/source-review.json`. The completed result review is recorded separately. No independent all-edge scan is claimed.

All inherited local hypotheses, hypothetical floors, odd-length restrictions, and graph-to-snake obligations remain. The retained additional-share comparison stays a separate zero-credit result. No new actual-snake bound is established by this source review.
