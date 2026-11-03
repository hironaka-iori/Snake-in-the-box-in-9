# Zero-credit source and result review

Status: **PASS_SOURCE_REVIEW_RESULT_AVAILABLE**. The complete source diff from the pinned milestone140 evaluator has been inspected. No source correction is needed. The terminal saved-result review also passed; its separate scope and findings are recorded in `audit/result-review.md` and `data/result-review.json`.

The new profiles use the original weights `base_weights[name] + shared`, multiplier 1, and occurrence credit 0. Their reported mean, range, cycle weights, zero-range comparison, and charge comparison all use these original units. Occurrence flags remain diagnostic and contribute zero weight. The allowance field remains 24, while its numerical contribution is zero.

The milestone139 reconstruction is preserved: its weight hashes still use `3*(base_weights[name]+shared)+83*event`. The historical four-cycle comparison retains the same scaled expression. These are the only two remaining `83*event` expressions. The old removal and weight checks occur before the weak exclusion and before the new zero-credit profiles are evaluated.

The weak-exclusion mask is unchanged. Its proof gate now explicitly reads milestone140's `data/proof-completion.json` and restricts the source and receipt paths to milestone140. The completion record has status `PASS_ACTUAL_012032_WEAK_EXCLUSION`. The pinned source and successful audit receipt identify `Snake9.Weak140.actual_weak_counts`, whose actual-snake hypotheses are the fitting shape `012032` and counts `(3,<=5,4,<=5,3)`. The source statement and matching source/receipt hashes were inspected. No Lean compiler or proof replay was run in this review.

The gate still runs before graph imports. The inherited all-edge potential checks, attained-cycle checks, overflow guard, predecessor checks, and final source-pin recheck remain intact.

For a cycle mean \(p/d\) in the original weights and integer potential range \(R\), the comparison is correctly

\[
B=\frac{1098960d+8p+R}{4200d+p},\qquad
B-235=\frac{R+111960d-227p}{4200d+p}.
\]

At mean 496, the strict condition is \(R/d<632\). Equality gives 235. The implementation's target fields use mean at least 496 and range below 632, and its reported comparison uses the actual computed mean and range. Five rational test cases were checked independently and recorded in the JSON review.

Both profiles retain their inherited count/share hypotheses, hypothetical six-count floor 25, odd-length restriction, and remaining graph-to-snake obligations. The zero-credit change does not justify direct application to even-length snakes or establish a new global upper bound.

All source pins, the source-review verdict, and arithmetic checks are recorded in `data/zero-credit-source-review.json`. No graph array or potential was loaded during this source-review stage. No independent all-edge scan is claimed.
