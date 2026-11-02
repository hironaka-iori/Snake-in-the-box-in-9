# Preserved attempts and verification boundary

Preparation initially used only the source basename for archived copies.
The CNF and semantic modules share the filename Q012A11.lean, so an equality
assertion stopped preparation before the semantic source could overwrite the
CNF copy. The corrected layout retains each full original path. The first
flat copy remains preserved and is the same CNF source; it is unused.

The work CNF is written with explicit LF bytes, so the recorded digest is
the actual solver input digest on Windows. No solver ran on the earlier
text-mode version. The solver attempt is preserved separately from the
subsequent Lean checks and supplies no standalone theorem claim.

The first 18 Lean modules passed. The final combined wrapper then failed
on a missing shared LocalWindowSat.CycleWindow471 object because the new
LocalWindowSat directory shadowed the shared namespace directory. Those
sources, compiled objects, logs and environment pins were preserved.

The second attempt places recovered imports under Recovered107 and uses a
separate output directory. An exact audit confirms that only import paths
changed. All 19 modules pass, including the final reference-list statement.
The audit preserves the first attempt without treating its failed wrapper
as a successful composition.

The independent RUP check uses plain signed literals and clause IDs, rather
than the generated packed tree representation. Every input clause matches
the archived Lean raw list after decoding. The final theorem's axiom audit
covers the semantic check, contradiction, all seven segment assertions and
four reference-list conclusions.

This round closes one selected entry. It does not prove the remaining
reference entries, the full graph potential or the five conditional local
share bounds. The active graph batch was neither restarted nor modified.

The separate alternative-source audit initially counted every JSON file in
two metadata directories. These directories also contain summaries and
entries outside the current catalogues. The initial assertions stopped
before producing a result. The corrected audit selects exact catalogue keys,
omits summary JSON, and verifies the 320 corresponding metadata hashes.
It reproduces the independently reviewed 143-key overlap and next-candidate
clause identity. No proof or solver job was affected by this correction.
