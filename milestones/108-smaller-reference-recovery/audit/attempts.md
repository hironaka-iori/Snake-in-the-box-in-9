# Attempts and verification boundaries

1. The first clause parser expected `noncomputable def cnf`, whereas the older
   source uses `def cnf`. It failed before launching the solver. The parser now
   accepts either declaration without modifying the archived source.
2. The solver regenerated the exact core contradiction in 0.078 seconds on
   this run. Its UNSAT report alone is not treated as a proof.
3. Six case modules passed Lean; the exact-key wrapper then passed with nine
   axiom reports. Unique import prefix `Recovered108` was used from the start.
4. The relaxed semantic theorem passed in a separate module. It changes six
   unused counter limits inside a local expression and introduces no definition.
5. The first seven-key coverage attempt failed because the kernel could not
   reduce the well-founded implementation of the logarithm in the centre
   calculation. Its source snapshot and failed log remain saved. The repaired
   proof first uses the existing equality with the computable centre list,
   then checks the finite containment statements. Its final module passes.

All nine final successful module receipts, source snapshots, logs, dependency
hashes and fifteen axiom reports are independently checked by `scripts/audit.py`.
Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` occur.
Failed elaborations are preserved as failures and do not enter the successful
receipt set. Shared support objects are reused; no clean rebuild is asserted.

The independent reviews are source inspections. Their proposed proof text and
parent-reported status are distinguished from actual compiler evidence. The
final proof summary and verified receipts determine the checked scope.

The running milestone 104 batch is observed without editing its active files.
An immutable observation and newly completed receipts are saved separately.
Its running state is not evidence of full graph certification.
