# Independent selected-row cycle audit

Status: `PASS_SELECTED_CYCLE_OLD_WALK_AND_FULL149_AUDIT`.

The retained nine-cycle has weight 4462 and zero uniform-credit occurrence events. The earlier nine-edge walk has weight 3861 and zero occurrence events. Together they exclude a comparison below 235 for every nonnegative mean and nonnegative uniform occurrence credit in this fixed floor-17 profile. In particular, mean 496 is infeasible at every potential range.

## Checked source evidence

The audit streamed the five required original NPZ columns in blocks of at most 1 MiB: `U`, `V`, `weight`, `direction` and `count_code`. Each complete column hash matches the source metadata, and the archive and input hashes match the recorded evidence. The native milestone-155 resource helper required at least 1.5 GiB free memory before column reads. Only 56 unique selected rows were retained.

The selected rows cover the complete saved 149-edge walk, the repeated nine-cycle and the earlier nine-edge walk. For every row, the audit checks retention in the accepted milestone-144 mask and recomputes the floor-17 weight from the original source weight, decoded chronological counts, suffix share recognition and the independently reviewed scalar shared-bonus formula. Source and target vertices join. Adjacent direction words agree on their eight-direction overlap after canonical renaming, and adjacent stored counts agree on their five-count overlap. The cycle's final-to-first overlap is also checked.

The saved 149-edge walk has total weight 73271 and exact deficit

\[
149\cdot496-73271=633.
\]

All its recorded endpoints, weights and share-17 flags agree with the original selected rows. Its occurrence count is zero. This directly verifies the saved witness; the disk journal was not replayed during this audit.

## Retained nine-cycle

| Source row | Source vertex | Target vertex | Suffix shape | Weight |
| ---: | ---: | ---: | :--- | ---: |
| 991858 | 216752 | 305186 | 012301 | 376 |
| 1272641 | 305186 | 688049 | 012304 | 736 |
| 3005579 | 688049 | 1173417 | 012034 | 497 |
| 943614 | 1173417 | 1457336 | 012310 | 372 |
| 1340646 | 1457336 | 1333493 | 012034 | 737 |
| 3609461 | 1333493 | 1360255 | 012304 | 256 |
| 1726634 | 1360255 | 1505276 | 012301 | 376 |
| 487872 | 1505276 | 1387853 | 012304 | 736 |
| 3070840 | 1387853 | 216752 | 012304 | 376 |

All nine shared bonuses are zero. No edge has suffix shape 012032, so the cycle has neither a count-conditioned share-17 match nor a uniform-credit occurrence event. Its two 012034 rows each lost one unit when the floor decreased from 18 to 17. The earlier total was 4464; the present total is 4462.

Summing the potential inequalities gives

\[
9\mu\le4462,\qquad \mu\le\frac{4462}{9}<496.
\]

The event count is zero, so adding nonnegative uniform occurrence credit does not change this cap. At mean 496, the cycle has deficit two. Repeating it produces arbitrarily large walk deficits; consequently, no finite-range potential exists at that mean for this profile.

## Obstruction for all nonnegative means and credits

The earlier nine-edge walk has source rows

`4001343, 4684655, 3607986, 1742134, 491026, 3069298, 987251, 1275893, 3049938`.

Its recomputed weights are

\[
(252,377,496,496,616,496,496,376,256),
\]

with sum 3861. Its event count is zero, so every valid potential with uniform occurrence credit \(C\ge0\) still satisfies

\[
R\ge9\mu-3861.
\]

For \(\mu\ge0\), the comparison therefore satisfies

\[
\frac{1098960+8\mu+R+24C}{4200+\mu}
\ge\frac{1095099+17\mu+24C}{4200+\mu}
\ge\frac{1095099+17\mu}{4200+\mu}.
\]

The last expression decreases with \(\mu\): its derivative numerator is
\(17\cdot4200-1095099=-1023699<0\). Using the cycle cap gives

\[
\frac{1098960+8\mu+R+24C}{4200+\mu}
\ge\frac{9931745}{42262}
=235+\frac{175}{42262}>235.
\]

Thus retuning the mean, potential range or nonnegative uniform occurrence credit cannot retain the conditional integer conclusion 234 after this floor reduction, with the graph, other weights and comparison unchanged. This lower bound is an obstruction; attainment and the exact best comparison were not established.

## Scope and files

The audit ran no optimizer, full graph reconstruction, all-edge inequality scan, solver or Lean process. The unused source history column was not loaded. The five required columns were streamed for hash verification and selected-row extraction only. An initial run caught an arithmetic transcription error in the final rational assertion; the corrected audit completed with all assertions passing. Accepted source and result files were unchanged.

All geometric, count-rule, six-count, reference and graph-to-snake assumptions remain. The obstruction is a statement about this retained finite graph and weight profile. It does not establish a new bound for arbitrary snakes.

The full selected-row data, input hashes and exact checks are recorded in `cycle-audit.json`; `cycle-audit.py` reproduces the bounded audit. The script hash is

`78142e87f838b908d843f732c10d5cdc8eaa2f5a82c88f8b4efb87309609b249`.

The completed JSON hash is

`7daac3e9fdb991b31e93b9f2aec6afdb01238c4ae3712d61044e4efbf3e9d98d`.
