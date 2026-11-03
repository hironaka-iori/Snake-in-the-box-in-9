# Review of the exclusion and occurrence-credit model

Status: **PASS_STATIC_MODEL_AND_ARITHMETIC_REVIEW**. The pinned preparation script and generated evaluator implement the requested mask, suffix credit, and scaled comparison correctly. No change is requested. This review did not load graph or potential arrays, run the graph evaluator, run a solver, or run Lean. It does not certify the pending full-graph result.

## Exact mask and credit

The evaluator reconstructs milestone131 before adding the new rule. Lines 356–363 compare the predecessor removal set, edge count, and both retained-weight hashes. Its new deletion at lines 380–382 matches the full canonical chronological word `012301430` and the six stored symbols `(6,3,3,3,5,2)`. These are counts at local vertices 3 through 8. Symbol 6 means an actual count at least 6. The mask uses no reversal of the six-count list and no stronger six-direction cap exclusion.

The inspected actual theorem, `Snake9.LocalWindow.CycleBase138.actual_cycle_row` in `ActualBase138Minimal.lean`, has exactly these count hypotheses and a fitting nine-transition window. It has no parity or endpoint restriction. The evaluator checks the proof-completion status and final source hash and records its relevant sources and receipts. This review checks that interface; it does not independently repeat their Lean compilation.

The event at lines 384–387 uses only suffix directions `word[3:9]`, with shape `012032`, and count pair `digits[:,2], digits[:,4]`. Those counts are at local vertices 5 and 7, or offsets 2 and 4 within the six-direction suffix. This agrees with `Snake9.ActualCount137.low_pair_count_le_twenty_four`. The six-direction word has the same canonical shape under reversal, and reversal swaps the relevant pair. Thus the shape test does not change the sum condition.

The event requires both symbols below 6 and their sum at most 9. This exact-count guard is essential: stored pair `(6,3)` could represent actual pair `(7,3)`. Its clipped sum cannot certify the actual upper bound. Leaving other potentially qualifying pairs with a clipped symbol uncredited is safe for an allowance bounding all qualifying actual windows.

After the inherited odd-length pair-floor-nine deletion, every retained credited edge has pair `(4,5)` or `(5,4)`. The script asserts absence of retained credited pairs with sum below 9. Together with the digit domain and guard, this implies the stated two pairs. Prefix matches receive no additional credit, and reversal does not duplicate a Boolean event.

The weights at line 415 are exactly

\[
W_e=3w_e+83\,\mathbf 1_e,
\]

where \(w_e\) is the unchanged milestone131 profile weight, including its existing shared maximum, and \(\mathbf 1_e\) is the suffix-event indicator. This represents additive credit \(C=83/3\) in the original units. The new credit is added after the existing shared maximum.

## Scaled comparison

For integer weights \(W_e\), let the certified minimum mean be \(p/d\), with \(d>0\). The retained potential check is

\[
dW_e+h(u)-p-h(v)\ge0.
\]

If its integer range is \(R=\max h-\min h\), the original-unit mean and range are

\[
\mu=\frac{p}{3d},\qquad \rho=\frac{R}{3d}.
\]

Given the inherited charge comparison and allowance of 24 credited occurrences, line 442 correctly computes

\[
B=\frac{3\cdot1098960d+8p+24\cdot83d+R}{3\cdot4200d+p}.
\]

The allowance term includes the factor \(d\). The output at lines 452–454 distinguishes the scaled mean from \(\mu\), retains integer range \(R\), and reports the original range \(\rho\). The zero-range comparison uses the same scaling and allowance.

The exact difference from 235 is

\[
B-235=\frac{R+337872d-227p}{12600d+p}.
\]

At proposed original mean \(3011/6\), the reduced scaled mean is \(3011/2\), so \(p=3011,d=2\). Hence

\[
B-235=\frac{R-7753}{28211}.
\]

The strict target is therefore \(R<7753\), equivalently \(\rho<7753/6\). Equality yields 235 and does not yield integer upper bound 234. If the graph finds a different mean, its actual certified \(p,d\) must be used. The script computes the comparison from those values rather than assuming target attainment.

## Saved-cycle constraints and preserved checks

The saved completed four-cycle has two suffix events in four edges, so its original mean becomes

\[
488+\frac12\frac{83}{3}=\frac{3011}{6}.
\]

The archived 18-cycle has no `012032` match at either placement and retains current comparison mean \(3011/6\). Both survive the new deletion. The evaluator checks these facts at lines 388–390 and 397–404. These cycles cap the new completed-profile minimum at the target; they do not establish attainment.

The former seven-cycle has no credited event and had completed-profile mean \(3453/7\). The new ordinary exclusion removes its edge 992157 while retaining edge 1273862. The implementation explicitly checks these two edges. This deletion changes the fixed-graph assumptions of the earlier milestone132 credit limitation; that result remains valid for its original graph.

Inspection of the complete diff against the pinned milestone131 evaluator found only the planned wrapper, predecessor validation, proof pins, mask, credit, scaling, cycle diagnostics, and reporting changes. The old removal reconstruction, shared maximum, profile floors, algorithm, and potential verification remain intact. The integer overflow guard at lines 423–424 uses the new scaled weights; all-edge inequalities, attainment, and source rechecks remain in place.

The preparation script and generated evaluator both parse successfully. Their actual hashes agree with the preparation receipt. The source generator's replacement points are uniquely asserted. No generator was executed during this review.

## Inherited assumptions and remaining work

Both profiles retain milestone131's count-sum hypotheses, its hypothetical six-count floor 25 for `0123104`, and the odd-length assumption behind pair-floor-nine deletions. The `conditional_floor18` profile also retains its extra count-free floors. A proved ordinary exclusion and an occurrence allowance do not discharge those other hypotheses.

The occurrence theorem itself applies to arbitrary actual snakes and any finite set of fitting canonical six-windows with pair sum at most 9. The selected suffix windows are a subset of these windows. Its actual cardinality conclusion is 24, and the script checks the saved verification record. The odd-length restriction enters through the inherited graph deletion, not through this occurrence theorem.

Consequently, this graph cannot be applied directly to even-length snakes. Any all-length conclusion needs its own stated argument, including any required truncation step and the actual-snake charge comparison. The full graph-to-snake assembly and inherited conditional hypotheses remain separate obligations. The script's scope statement preserves this distinction and asserts no new actual-snake upper bound.

## Independent checks performed

- Exhaustively tested all 441 actual count pairs in `{1,...,21}^2`: the event guard always implies actual sum at most 9. Under sum at least 9, precisely `(4,5)` and `(5,4)` receive credit.
- Checked the rational comparison at integer ranges 0, 7752, 7753, and 7754. The first two are below 235, the third equals 235, and the fourth exceeds it.
- Independently derived the general numerator difference and scaled-to-original conversions.
- Read the actual theorem statements for the nine-window exclusion and occurrence bound; their coordinate offsets agree with the two masks.
- Compared the entire generated evaluator with its pinned predecessor and verified all three preparation hashes. These are static checks; the all-edge and attained-cycle results are pending the separately run experiment.

## Source pins

| Repository-relative path | SHA-256 |
|---|---|
| `milestones/139-exclusion-occurrence-credit/scripts/prepare_graph.py` | `2d6c9cec482cd88597e33e3f4535b7027acbddff9be9700f1c4b17b3634e1509` |
| `milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py` | `c38a19a4e6288f8c1e88bbc9c004525527bc613339683157569c88f0d0e244c7` |
| `milestones/139-exclusion-occurrence-credit/data/preparation.json` | `b57f9b80b73a4936979a86fba7267ffc967f15c4122a03f19d9dd6700ac7a4c0` |
| `milestones/131-odd-pair-six-count/scripts/evaluate_graph.py` | `86386a1a117dfd9080b7360f9b99a641054fe9ea174baa9a2b532b33199e52ac` |
| `milestones/137-actual-block-assembly/lean/ActualCount137.lean` | `6c663ff371f792efe9078f34b3a1bca87334c8e1f5716ef4653e4c544b11eaaf` |
| `milestones/138-seven-cycle-endpoints/lean/ActualBase138Minimal.lean` | `d024e01bf668a7d67b71b9c4d015be9249a187534575af6ad901d7ace3edb078` |
| `milestones/138-seven-cycle-endpoints/lean/Credit138.lean` | `2ea8baa70e3542918325d1d2f4a2bfe6ec4c11b33200c9d62fc7b6d3c88007fc` |
| `milestones/138-seven-cycle-endpoints/audit/credit-next.md` | `a11de0cbeea4143e2ec0f125b576f02dcd31e33cc95e1f4da22daf990742c513` |
