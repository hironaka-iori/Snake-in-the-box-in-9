# Case 7302: count-free share 20 for 012034

Status: semantic interpretation checked; selected refutation replay in progress.
The final arbitrary-snake theorem is pending. Do not add this case to the
completed catalogue until `data/proof-audit.json` reports
`PASS_LOCAL_SHARE_THEOREM`, including geometry and reversal.

The six directions are (a,b,c,a,d,e), with five distinct coordinates below
nine. The target is total scale-12 share at least 20 over the five internal
vertices, with no extra singleton-count condition. The reversed window is
included. Its native cap 19 instance has five universal count bounds [0,21]
and no cycle cuts.

All 121 clause shards, their composition and support passed Lean: 127 modules.
The selected compact refutation contains 389,216 derived clauses and 25,783,817
hints, compared with 548,140 clauses and 33,454,760 hints originally. Both the
candidate and selected export simulations passed. The input clauses and
semantic sources are unchanged. The selected export uses 15-bit words,
27,815 slots, 858 segments and 143 checking modules.

Continue using this case's existing `scripts/complete_share.py`. Inspect the
actual running process before starting it; the active task observation is in
`../../../83-012034-share-certificate/data/checkpoint.json`. The driver resumes
source-matched successful modules and proceeds to the final geometric and
reversal wrappers. Never run two drivers for this case simultaneously.

After the driver finishes successfully, run `scripts/audit_share.py`, then
the shared catalogue's `scripts/archive.py 7302` and `scripts/restore.py 7302`.
Only then update the combined catalogue and recompute the completed-share
comparison. The native input remains under milestone 72/critical-current.

`data/pending-checkpoint.json` records the exact selected sources, original
proof provenance, compact refutation and semantic receipts. Its archives
preserve all corresponding bytes. Compiled objects remain local. The active
completion record can be newer than a saved observation; inspect live state.
After a fresh checkout, run milestone83's `scripts/restore_pending.py` to
restore the source and proof archives. It rejoins the three source-archive
parts and checks every member before writing. Rebuild dependencies and
semantic modules on a new host; their compiled caches are not stored in Git.

All 1,135 selected Lean sources are archived. The original CNF and LRAT,
generation/export metadata, and unsliced-source hash manifest are also archived.
The superseded 1,303-file unsliced Lean export remains local in
`build/lrat-slice-21fb3e526fcb/original-lean/` and is excluded from Git archives.
Exact regeneration of that superseded tree was not rerun in this round and is
unnecessary for resuming the selected replay.

The existing single-target comparison is conditional: adding this unproved
floor gives mean 9259/19 and integer comparison 235. It does not establish a
new global upper bound. See the [milestone 83 report](../../../83-012034-share-certificate/README.md).
