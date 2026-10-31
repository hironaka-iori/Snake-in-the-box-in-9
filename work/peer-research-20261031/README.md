# Q9 global cuts, solver and Lean audit snapshot

Research snapshot prepared on 31 October 2026 for `research/q9-global-cuts-lean-audit`.

No new numerical Q9 upper bound is proved. The two guarded cap254 queries remain UNKNOWN. Their final bounded batches retained 374105 and 342243 proof steps respectively; these later batches must not be confused with the independently reviewed 397592-step round-two snapshot. Saved review notes identify their exact hashes and scope.

## Included

- Exact square charges and counting arguments, necessary-condition encoders and proof-producing Python solvers, independent RUP and geometry checkers, guarded global cutsets, controls and peer reviews.
- The one-centre cap21 DIMACS/LRAT certificate and its geometric-cut manifest. Its Python check supports the explicit local score22 exclusion, not a new global upper bound or a complete Lean bridge.
- Small Lean source modules, historical remote Lean 4.19.0 receipts and negative controls. Larger receipts are compressed without changing their bytes. Full-certificate Lean replay and the new snake-to-CNF Lean bridge remain unfinished.
- Four dated PDF report snapshots. They describe their own evidence dates and are not fresh compiler receipts.
- Exact original `wincert.py` and bank fixtures in their expected relative layout, attributed to the existing repository and its cited source dataset.

## Reproduce the small checks

Run from this directory with Python 3.12 or later, without `-O`:

```sh
python restore_receipts.py
python work/branch241-lean/check_remote_receipts.py
python work/branch241-review/verify_certificate.py --rebuild
python work/branch241-literature/global_cutsets.py
```

The first audit validates saved historical remote receipts and source identities; it does not run Lean. The certificate check independently replays RUP hints after rebuilding the mathematical CNF. The global-cutset program checks the small-cube controls stated in its source.

## Intentionally omitted artifacts

Native toolchains, third-party paper PDFs, generated full Lean replay files, very large search checkpoints and build objects are not included. Large search continuation commands therefore require their archived checkpoint fixtures; this snapshot does not promise that every historical experiment can resume from source alone. The source manifest records all included bytes; separate omitted-artifact hashes identify large local evidence.

## KEEP=96 continuation status

The remote KEEP=96 branch was inspected at `9c2ff68f90d6d0e85ff7512a5d024ba37610dddc`. Its restricted target covers all 262 oriented 96-vertex bank prefixes. Its README reports a historical stop after 83 entries / 24 representatives and an eight-step proof-batch repair with entry179 as gate. This snapshot does not contain a completed KEEP=96 formalization or claim fresh audits for those 83 entries. On this machine, Windows denies credential enumeration for native Git and application control blocks the installed Lean executable. GitHub connector access works. No native clone, fresh Lean campaign, or completed aggregate theorem is claimed.

Root repository README, COLLABORATION, paper and existing proof projects are unchanged by this isolated subtree addition. Consult the maintained upstream sources for current global bounds.
