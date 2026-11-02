# Independent review of the single-target comparison

Review date: 2026-11-02. Scope: bounded source, provenance, receipt, and arithmetic review. No solver, Lean compiler, graph reconstruction, or exhaustive edge comparison was rerun. Only this review file was written.

## Finding

No defect was found in the reviewed claim. The archived finite graph, with the single additional local premise that shape `012034` has five-centre share at least 20, has certified minimum cycle mean

\[
\mu=\frac{9259}{19}.
\]

The certificate is computational: the saved comparison receipt records all-edge potential verification and an attaining cycle. The three checked Lean statements establish conditional budget arithmetic. They do not establish the pending local share theorem, the interpretation of arbitrary snakes as paths in this graph, or a new global upper bound.

## Single-premise and comparison scope

Reviewed `scripts/compare_target.py`, `scripts/verify_comparison.py`, `data/assumed-012034x20-model.json`, and `data/comparison-audit.json` under this milestone, together with milestone73's completed `data/proved-model.json`.

The generator accepts exactly `--assume=012034:20`. The verifier requires the completed baseline to have no additional share assumptions, requires the new assumption list to contain exactly this target, and checks that the local proof-audit dictionary is unchanged. Independent inspection confirmed that the floor dictionary differs only by the new `012034:20` row. All six comparison input hashes and all five local proof-audit hashes match the current files.

Both scripts use the minimum of the forward and reversed canonical six-direction shapes. The weight is the maximum of the existing edge weight and the count contribution plus the applicable share floor. The scripts do not add competing share floors together. The verifier reconstructs both baseline and target weights, checks both hashes, checks unchanged source-array hashes, and checks that weights never decrease.

The receipt's **1,043,097** newly raised edges compares the assumed target against the completed milestone73 model. The model's separate `improved_edges` value **3,579,688** compares against the older source graph. These are different baselines and must retain their descriptions. This review checked the counting expression and matching receipt provenance; it did not recount the graph's 4,947,008 edges.

## Exact graph certificate and arithmetic

The verifier checks every inequality

\[
9259+\pi(v)\leq 19w(u,v)+\pi(u).
\]

Summing these inequalities around any directed cycle gives mean at least \(9259/19\). It also checks every saved cycle edge against the graph arrays and verifies cyclic incidence, so a matching cycle supplies equality. Independently, this review confirmed the saved cycle has 19 edges, closes, and has total weight 9259. No assertion about realization of this cycle by an actual snake is made.

The compressed potential's file hash, decompressed hash, length 1,601,856, minimum zero, and maximum 11,301 were independently checked. Thus the potential range is **11,301 in the integer scale**, or \(11301/19\) in the unscaled edge-weight units.

Combining the stated budget and path-potential premises yields

\[
(9259+19\cdot4200)m
 \leq19\cdot1098960+8\cdot9259+11301,
\]

and hence

\[
m\leq\frac{20965613}{89059},\qquad
235<\frac{20965613}{89059}<236.
\]

The resulting integer conclusion remains \(m\leq235\). The strict criterion for 234 fails even with zero potential range because

\[
111960\cdot19-227\cdot9259=25447>0.
\]

All these arithmetic values were independently recomputed using exact rational arithmetic.

## Lean receipt and hypotheses

`lean/ConditionalTarget.lean` proves the integer conclusion only for natural \(m,W\), assuming \(8\leq m\), \(W+4200m\leq1098960\), and \(9259(m-8)\leq19W+11301\). The lower hypothesis on \(m\) protects the natural-number subtraction. These budget and potential premises are explicit and are not derived from an arbitrary snake in this file.

The second theorem is a rational arithmetic obstruction with explicit nonnegative denominator and range hypotheses, plus the cycle ceiling \(19p\leq9259d\). It does not prove that ceiling for every conceivable modified graph. Its application here uses the attaining cycle of this particular assumed graph. The third theorem checks the deficit 25,447.

The successful receipt records three printed axiom audits using only `propext`, `Classical.choice`, and `Quot.sound`, with no axioms for the numerical deficit theorem. The current Lean source, compiled object, and log hashes match the receipt. The receipt also pins the current comparison audit. No fresh compilation was performed during this independent review.

## Slicer provenance

`data/slicer-source.json` identifies milestone73's `scripts/slice_lrat.py`, originally targeting case7305, as the template. Its recorded template hash matches the current original file. An exact text comparison confirms that milestone83's slicer differs only by replacement of case7305 with case7302 and by adjustment of the task/shared-catalogue root expression. The slicing, dependency tracing, simulation, and selection algorithms are unchanged by that adaptation. This verifies preservation of the original case7305 slicer; the provenance file contains no claim about a separate case7310 source. Slicing and successful simulation alone do not discharge the pending Lean certificate replay.

## Receipt fingerprints

- Comparison audit: `8d3cedcb25436fab7257d5cf36f2eb2e07d7f3baf52fab3aaaba803dcf4b385b`.
- Lean arithmetic audit: `f29a33df320f10947f7073f0b6c62a2adcbc6b4cf99b63ac5b61cfba1d28162d`.
- Assumed model: `f64ad918df0c725b3773b5f6f896162af4ea8044ab031489812076d0ca037a85`.
- Slicer provenance: `4918c0cbd95d67644684b1f0b46073803c248b26d1fe688a154777694f007b39`.
- Adapted slicer: `b1516105a10c8100307096fcf6980e605c70434a799b1d36b2039b0effba2608`.
- Original case7305 slicer: `876eb5f8deb38f758c76f61501f9b96b3d5ab7c3e52bea13d8785a4222750dba`.

The justified result is an exact conditional finite-graph improvement from mean 483 to \(9259/19\), with the same conditional integer bound 235. Completion of the case7302 local theorem and the remaining graph-to-snake obligations are separate tasks.
