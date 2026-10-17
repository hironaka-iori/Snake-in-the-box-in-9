# KEEP=112 formal certification

All 262 oriented bank entries and all 86 representative regions passed Lean
4.19.0. The final aggregate compiled on 17 October 2026 at 08:03 Shanghai time.

For every bank orientation, a nine-dimensional induced path sharing its first
112 vertices cannot have 192 or more edges. The corresponding reversed-end
statement also holds. Thus every snake satisfying one of these specified
end-segment hypotheses has at most 191 edges. These are conditional results;
they do not assert global optimality or coverage of arbitrary snakes.

`bank/Bank112Results.lean` exports:

- `Snake9.Regrowth.Bank112.bank_no192`
- `Snake9.Regrowth.Bank112.bank_no_long_prefix`
- `Snake9.Regrowth.Bank112.bank_no_long_suffix`
- `Snake9.Regrowth.Bank112.bank_end_segment_length_le191`

Each aggregate theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Every bank-indexed entry theorem has its own recorded axiom audit.
There are no admitted proofs, native decision shortcuts, or custom axioms in
the audited generated source modules.

The argument connects suffix geometry to finite Boolean constraints, checks
retained RUP inference steps by kernel reduction using proved soundness lemmas,
and reuses representative exclusions through separately checked cube
translations and region inclusions. Exact bank-prefix identities are also
checked in Lean. Solver outcomes alone are not used as theorem evidence.

## Evidence and reproduction

The evidence in `outputs/lean112/` includes `bank-proof.json`,
`bank-module-checks.json`, `bank-final-audit.json`, the first-entry receipts,
and `bank-logs/Bank112Results.log`. The batch records cover 7,676 modules;
the first geometric proof and its original Boolean certificate additionally
have 53 and 150 checked modules respectively. These are build-record counts,
not counts of independent mathematical claims.

`python work/lean112/audit_bank.py` validates saved source/object hashes,
direct-import hashes, all 262 entry audits, the four aggregate audits, and
the original first-entry evidence. This is an audit of the saved build, not
an independent clean rebuild. Compiled objects are local build products and
are not stored in Git.

The production sources are in `work/lean112/`, `work/lean112/bank/`,
`work/lean/sat-first-checked/`, and the existing `work/final_lean/` dependency
tree. The resumable Windows build entry point is `work/lean112/start-bank.ps1`;
its runtime paths and the dependency search paths in `run_bank.py` must match
the local Lean 4.19.0 installation. Existing verified modules are reused only
when source, object and direct-import hashes match. A fresh environment must
first build the existing dependencies and original first-entry proof; the
saved audit cannot replace those compilations.

The KEEP=144 work is preserved. KEEP=96 feasibility work is separate and is
not incorporated in this certification. No claim of literature novelty is
made by this build result.
