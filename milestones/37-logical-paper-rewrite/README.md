# Logical manuscript revision

Date: 24 October 2026. Baseline: `ffdf1b94403396a1b8ddaffdae419bb897ba5cf8`.

The existing manuscript was rewritten in place after the completed milestone 36 research round. The repository paper and the already-open editor source are identical. Authors and the complete preamble, including local hyperlink and PDF-author settings, are preserved.

The main argument now follows its mathematical dependencies:

1. Definition, edge/vertex convention, and the explicit lower bound.
2. A direct proof of the exact square identity, positivity, endpoints, and missing-corner counts.
3. Necessary local conditions, the complete 175-row exclusion family, the finite potential inequality, its explicit telescoping sum, endpoint terms, and the bound 238.
4. Sharp two-position count inequalities, empty-square shares, a forced three-square bonus, and overlap restrictions.
5. Conditions still needed for a stronger global bound, construction criteria, and the limitations of the 196 conjecture.
6. Verification status, distinguishing the independently rebuilt 241 theorem from the incrementally audited 238 theorem.

The detailed geometric classifications, intermediate bounds, search records, local-model diagnostics, threshold clauses, and explicit witnesses are retained in appendices. Long finite classifications are still identified as outlines where the printed account omits individual branches. The full 175-case exclusion catalogue is printed; the millions of certificate steps and the 44,064-entry potential remain supplementary proof data, with an immutable repository citation.

## Checks

- All original labels and theorem statements are retained, apart from four explicitly restated statements with unchanged mathematical content.
- The entire printed witness appendix is unchanged.
- All 175 printed exclusion rows agree with the input to the checked proof.
- An independent enumeration checks 1,026,432 candidate state transitions, including 700,433 permitted transitions, on 34 seven-direction shapes and 132 induced eight-direction words. The saved potential ranges from 0 to 10; the exposition uses the proved bound 15 to match the existing 52 boundary correction.
- Five Lean arithmetic lemmas check the exact census deduction, the boundary correction, the endpoint/incidence deduction of 238, and the conditional 230/231 charge targets. These checks do not independently replay the 175 geometric certificates.
- Source checks verify references, citations, environment and brace balance, preserved authors/settings, and equality with the editor file. They do not replace LaTeX compilation.

The built-in compiler was attempted on the existing editor file. It failed before TeX started because the Windows unelevated restricted-token runner could not enforce split writable roots. No replacement PDF was generated. Rendered pages remain unverified.

## Reproduction

`scripts/rewrite.py` reconstructs the revision from the pinned baseline and updates the existing editor source. `scripts/check_potential.py` independently checks the finite inequality. `scripts/check_arithmetic.ps1` checks the five arithmetic statements in the existing Lean 4.19/mathlib environment. `scripts/verify.py` checks manuscript integrity and the verification receipts.

This revision changes exposition and records completed local results. It does not improve the global interval `191 <= a(9) <= 238`, complete the six-fours conjecture, or settle the exact optimum.
