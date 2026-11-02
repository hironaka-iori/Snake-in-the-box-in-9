# Rejected original count-proof import

The original CountChoice dependency closure imports ShareFrame. Combining it
with the current history bridge failed because LocalWindowShareBridge already
declares some of the same names. The failure is preserved in
`../logs/HistoryExclusions-original-import-collision.log`.

The original preparation source and object inventory in this folder are
historical diagnostics, not reproduction instructions. Do not run
`prepare_counts_original_attempt.py`: it was written for its former location
and would copy the rejected imports over the adapted sources.

The current proof uses `../scripts/prepare_compatible_counts.py` and fresh
checks of the extracted helper lemmas and three adapted count modules. The
current successful receipts supersede the original import attempt.
