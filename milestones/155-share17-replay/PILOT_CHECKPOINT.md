# Checked initial replay; full contradiction pending

All 34 pilot modules passed Lean. The exact shared core implies truth of the
initial clause tree and the complete checkpoint after 2,095 deductions and
6,002 propagation references. The 106 axiom reports and exact source, object,
log and dependency records were audited. This is an accepted proof prefix.

Full source generation produced 137 modules, including the accepted pilot,
covering 30,305 deductions and 1,754,767 references across 290 segments.
The full runner must validate and reuse the 34 existing receipts and check
only the remaining modules. Its final contradiction and the separate
actual-snake composition remain pending. No new global bound is claimed.

Use scripts/run_full_replay.py after full-execution-preparation.json exists.
Inspect data/full-replay-progress.json and its actual process before any
restart. On successful completion, run scripts/finish_full_replay.py, then
prepare and check the actual-snake composition in lean/ShareComplete155.lean.
Use the available full-auditor filename reported by the preparation record
if it differs from the name above. The completed theorem must retain the
five local count conditions and their reversed orientation.

The paper already states that the stronger contradiction is unfinished.
The last complete paper revision is 146; the next is due at milestone156.
