# Milestone 67: critical-family charge and improved boundary accounting

**Completed research round.** Empty-square charging now gives a conditional upper bound of **234 edges** in the complete recorded model. This is not an unconditional bound for all snakes. The maintained contributor-checked interval remains **191 ≤ a(9) ≤ 235**. The arbitrary-snake interpretation of the complete model and several inherited numerical premises remain to be discharged.

## Entire critical family

Milestone 66 left 70 critical states and 99 critical transitions. An independent check verifies every source potential inequality, identifies the entire tight cyclic component, and proves that its complement in the tight graph is acyclic. Thus the following study covers every minimum-mean cycle of that source model.

Keeping the identities of the overlapping source edges, including their history states, gives 148 states and 256 eleven-direction transitions. The 216 distinct direction shapes give 72 improved transitions. Their 63 improving geometric inequalities comprise 44 reused results and 19 new forced-absence proofs. All 63 have arbitrary-snake Lean statements.

There are also 25 rejected concrete direction words. Each selects a complete twelve-cycle. All 25 have direct Lean proofs of impossibility in an induced path; these checks support validity of the restricted context model.

The restricted graph's exact integer minimum rises from 18823/38 to 18893/38. Both restricted potentials and attaining cycles passed Lean. This restricted comparison alone would not justify changing the full-model estimate.

## Integration into the complete model

All 11,162 canonical induced eleven-direction words are enumerated. When a three-window signature has several compatible words, its credit is the minimum certified lower bound over all of them. If any compatible word lacks a positive certified bound, the new signature credit is omitted. This retains 47 new share rules, of which 14 have multiple compatible words. Contributions on the same centres are combined by their maximum.

The resulting graph has 1,601,856 states and 18,194,151 transitions. The strengthened rules improve 1,261,708 transitions relative to their source shares. The inherited direct count restrictions reject 17,161 transitions during the lift.

Its exact integer minimum is

\[
\mu=\frac{2482}{5},\qquad \frac{\mu}{120}=\frac{1241}{300}.
\]

The increase over milestone 66 is 201/190 in integer weight, or 67/7600 after normalization. An independently checked potential has range 3238 at denominator 5; a twenty-edge cycle attains the mean. The verifier reconstructs every transition, checks every potential inequality, and independently checks the geometry of every newly credited compatible word. These complete-model checks are executable integer computations. They have not yet been replayed as a complete Lean graph certificate.

## Boundary improvement

Let a snake have vertices v₀,...,vₘ, with m ≥ 8, and let αᵢ denote its singleton-square count at vᵢ. A nine-transition window charges the entering count at positions 8,...,m−1. The omitted positions are 0,...,7 and m.

The established adjacent internal count inequality gives

\[
\alpha_1+\alpha_2\ge4,\qquad
\alpha_3+\alpha_4\ge4,\qquad
\alpha_5+\alpha_6\ge4,\qquad \alpha_7\ge1.
\]

Both endpoints contribute at least four. Therefore the omitted singleton contribution is at least 21, improving the previous estimate 15. If B is the sum of entering truncated counts, T the total singleton count, Σ the total share and L the accumulated five-centre window credit, then

\[
B+21\le T,\qquad L\le5\Sigma,\qquad G=24T+\Sigma.
\]

Writing W=120B+L gives

\[
W+2520\le5G.
\]

Combining this with the square-incidence budget G+840(m+1)≤221136 yields

\[
W+4200m\le1098960.
\]

The exact potential would give, for every snake represented by the complete graph,

\[
2482(m-8)\le5W+3238.
\]

Eliminating W gives

\[
23482m\le5517894,
\qquad
m\le\frac{2758947}{11741}<235.
\]

Thus the conditional integer consequence is 234. At m=235 the left side exceeds the right side by 376. The old boundary estimate would instead give the right side 5521494 and allow 235. Small snakes with m<8 already satisfy the desired numerical bound.

Lean checks the seven-count inequality directly for arbitrary snakes, the indexed omitted-count sum, the aggregate arithmetic, and the conditional consequence. The potential premise in the final arithmetic theorem is explicit; this theorem does not assert that every snake already satisfies that premise.

## Evidence and remaining gap

- `data/verification.json`: independent coverage of the complete source critical family, all contexts and both restricted potentials.
- `data/full-verification.json`: independent reconstruction of all 18,194,151 complete-model transitions, geometric credits, exact potential and attaining cycle.
- `data/lean-audit.json`: 20 successful modules, 250 theorem dependency audits, only standard Lean axioms or no axioms. Imported proofs are reused.
- `lean/BoundaryCharge.lean`: actual-snake prefix inequality and conditional bound arithmetic.
- `data/full-analysis.json`: the original accounting is retained for comparison; the strengthened accounting is recorded separately in `full-verification.json`.

The next priority is proof closure: identify and discharge the inherited numerical rules, prove complete history recognition for arbitrary snakes, and replay a full potential certificate. The present mean and boundary estimate already suffice for 234 if these obligations are completed. Stronger means are no longer required merely to reach that target.

GitHub was refreshed to contributor revision `97851813be3cfe0a30ff2694db7b84d1772ce758`. Its new work includes replay-migration planning, a retargeted 234 automaton, a large-machine build specification and a partial 233 probe. The specification still requests the complete 234 proof and fresh older-chain rebuilds. No new global bound is adopted from those checkpoints.

## Reproduction

With the preceding milestone builds and Python dependencies available, run the scripts in this order:

1. `build_family.py`, `analyze.py`, `verify.py`.
2. `prepare_lean.py`, `prepare_validity.py`, `replay.py --resume`, `audit_lean.py`.
3. `build_full.py`, `analyze_full.py`, `verify_full.py`.

The two verifiers use separate reconstruction logic. Large generated graph arrays and compiled Lean files are ignored; generation scripts, mathematical sources, compressed potentials, data and audit receipts are retained.

This is research round 1 of 10 after manuscript revision 66. The existing paper and editor mirror are unchanged. The next full manuscript revision remains scheduled for milestone 76.
