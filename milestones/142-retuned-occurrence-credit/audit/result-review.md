# Independent retuned-credit result review

Status: **PASS_BOUNDED_SAVED_RESULT_REVIEW**. The saved result is internally consistent and agrees with the independently reconstructed source rows. The proposed target mean was not reached.

| Quantity | Verified value |
|---|---|
| Original mean | \(4406/9\) |
| Scaled mean | \(17624/3\) |
| Cycle length | 9 |
| Credited suffix events | 0 |
| Original potential range | \(5377/9\) |
| Integer potential range | 21,508 |
| Relaxation iterations | 31 |
| Comparison | \(9940859/42206=235+22449/42206\) |
| Integer part | 235 |

The range condition passed, while the mean condition failed. The nine-cycle's unscaled weights are

\[
610,\ 489,\ 376,\ 730,\ 369,\ 492,\ 600,\ 364,\ 376.
\]

Their sum is 4406. Every suffix-event indicator is false, and each scaled weight is exactly 12 times its original weight. Original edge IDs, state adjacency, directions, count symbols, shared charges, scaled weights, and all nine zero potential slacks were reconstructed and checked.

## Consequence for this uniform-credit model

The same nine-cycle survives unchanged for any nonnegative credit assigned only to the same suffix-event indicator. With the retained graph and base weights fixed, its mean gives

\[
\mu\le\frac{4406}{9}.
\]

For nonnegative credit \(C\), allowance \(B\), and range \(\rho\), with \(\mu\ge0\), the existing comparison has difference from 235 equal to

\[
\frac{1098960+8\mu+BC+\rho}{4200+\mu}-235
=\frac{111960-227\mu+BC+\rho}{4200+\mu}.
\]

The numerator is at least

\[
111960-227\frac{4406}{9}=\frac{7478}{9}>0.
\]

Thus changing this uniform credit alone cannot make this comparison fall below 235 on the fixed graph. Even with zero credit cost and zero range, the comparison at the cycle cap is

\[
\frac{4962944}{21103}=235+\frac{3739}{21103}>235.
\]

This is an elementary consequence of the checked saved cycle and rational arithmetic. No Lean invocation was performed in this audit. Its scope is the same retained graph, base weights, event indicator, and comparison; changes to exclusions or other parts of the model are outside this conclusion.

## Evidence and limits

The removal file is byte-identical to milestone141's, and both graphs contain 4,661,572 edges. Selected predecessor cycle rows were independently reconstructed for both zero-credit profiles. The earlier seven-cycle and archived 18-cycle both retain retuned comparison mean \(3011/6\); the new nine-cycle has a smaller mean.

The additional-share alternative remains milestone141's zero-credit profile, with mean 496, range 602, and comparison \(551765/2348\). It was not recomputed with the retuned credit and is pinned as a separate result.

Forty selected original rows were checked. Each original NPZ member was streamed once in chunks of at most 1 MiB and its complete data hash verified. No whole source array was loaded. The saved potential's hash, length, minimum, maximum, and cycle slacks were checked separately. Source, run, proof-gate, and predecessor pins agree.

The producer reports the full retained-weight hash reconstruction and all-edge potential certificate. This independent review recomputed selected weights and saved-cycle slacks only. It did not run a graph search, all-edge potential scan, solver, or Lean compiler. Iteration count 31 is recorded; no path witness or proof of optimal potential range was checked.

Inherited local hypotheses, the odd-length restriction, and the full actual-snake graph and charge assembly remain separate obligations. This audit establishes no new unconditional snake bound. Detailed evidence and exact source pins are saved in `data/result-review.json`.
