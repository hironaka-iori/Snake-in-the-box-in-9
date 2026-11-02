# Case 7305: count-free share 12 for 012310

The local theorem is complete as of milestone 80. All 465 modules and 100 printed
theorem audits passed, including the selected refutation, arbitrary-snake
geometry and reversal. `data/proof-audit.json` is the completed audit;
`data/archive.json` pins the exact checked-source and compact-proof archives.
Their restoration verified all 465 sources and both proof files. The combined
catalogue now uses this theorem. No case7305 proof process remains active.

The following partial-checkpoint files are retained as historical provenance.
`data/pending-checkpoint.json` hashes the compiled partial evidence, all generated
sources and three verified archives. `data/lrat-slice-selection.json` records the
reduction of the original proof to154,489 derived clauses and 9,394,822 hints.
Both the candidate and selected export passed independent Python simulation.
Every input clause and semantic source was preserved. The required checker
width remains15bits; no Lean replay speed improvement has been measured.

The archives are:

- `data/pending-lean-sources.tar.gz`: exact selected Lean sources, including
  uncompiled generated proof modules.
- `data/pending-compact-proof.tar.gz`: exact compact CNF and selected LRAT.
- `data/original-proof-evidence.tar.gz`: original proof, generation/export
  receipts and the original generated-source manifest. The original generated
  source tree is also preserved locally under `build/lrat-slice-ba39547a5d5e/`.

For reconstruction on a new host, restore the checked archive with the parent
`scripts/restore.py 7305`, then adapt toolchain/support paths and run the case's
`scripts/complete_share.py` followed by `scripts/audit_share.py`. On the current
host, successful unchanged source-matched receipts are reusable. Use one
completion driver per case. The old partial archives remain provenance.

Verify the partial archive against the present local files with the parent
`scripts/checkpoint_pending.py 7305 --verify`. On another host, inspect and
adapt absolute toolchain/support paths before attempting a proof rebuild.
