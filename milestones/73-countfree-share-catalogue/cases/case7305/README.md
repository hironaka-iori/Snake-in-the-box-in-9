# Case7305: count-free share12 for012310

This is a preserved partial proof. The completed catalogue does not yet use it.
The semantic CNF, data, structural checks, all86 clause batches, semantic
composition and satisfiability implication have passed Lean. The selected
refutation and final geometric/reversal wrappers remain to be checked.

`data/pending-checkpoint.json` hashes the compiled partial evidence, all generated
sources and three verified archives. `data/lrat-slice-selection.json` records the
reduction of the original proof to154,489 derived clauses and9,394,822 hints.
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

From the repository root, resume the existing case's
`scripts/complete_share.py --lrat-only`; after it succeeds, run the same script
without flags, then `scripts/audit_share.py`. Use one completion process at a
time. Never call a simulated proof or a successful partial build a finished
share theorem. A long checkpoint may require substantial memory; record a
timeout or failure precisely and retain the existing successful module records.

After the full audit passes, use the parent milestone's `scripts/archive.py 7305`
and `scripts/restore.py 7305`, then refresh integration, checkpoint and model.
The partial archives remain provenance. Before a new run, inspect processes
and current logs; no long case7305 replay is left running at this checkpoint.

Verify the partial archive against the present local files with the parent
`scripts/checkpoint_pending.py 7305 --verify`. On another host, inspect and
adapt absolute toolchain/support paths before attempting a proof rebuild.
