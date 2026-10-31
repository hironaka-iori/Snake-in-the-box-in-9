# Round-2 durable snapshot review — 2026-10-31

Independent complete replay PASS for these exact byte snapshots only. Each file was read once before decoding, and its path hash remained unchanged after validation.

| Shape | Snapshot SHA256 | RUP steps | Unit hints |
|---|---|---:|---:|
| 0120 | 72b559c2743da373c1e0a045d63d853d04fd64523e7ed1e267dd65b0e5936f76 | 210,850 | 12,309,367 |
| 0123 | f8638223bc68a6ed77c351fe7280a2ea7cc8d0534f30e85964146d48ba0941c2 | 186,742 | 11,387,557 |

For each snapshot the checker reconstructed every static clause, validated retained induced-cycle cuts, checked variable counts and integer vertex maps, verified stored static SHA256, and replayed the complete positive-hint proof. Both statuses are UNKNOWN, with no empty clause. No new bound or Lean replay follows. See the corresponding round2 JSON for machine-readable receipts and timing. Future replacements are outside this review.

## Batch source review before launch

The reviewed initial `run_guarded_batch.py` uses an exclusive per-shape lock file, finite round count, explicit positive child duration, and stops on a nonzero child exit or a terminal solver status. Per-round checkpoint output is delegated to the fully checked continuation runner. No mathematical soundness defect was found in this orchestration.

The initial implementation needs accurate budget/provenance wording: its lock is a batch-process concurrency lock, not a source-code lock, and does not stop an independent manual invocation of `continue_guarded.py`. A 400,000-step comparison before each slice is a starting threshold, not a strict final proof-length bound: a slice beginning below 400,000 can overshoot it. The source should reject nonfinite duration values, and should verify source hashes at each child launch if source locking is intended. Current concrete duration 120 and four rounds avoid the nonfinite-input issue. These findings were sent to the parent before launch. Any later edits require their own source-hash receipt.
