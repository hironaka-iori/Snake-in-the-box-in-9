## KEEP=96 feasibility

Investigates whether the first 96 vertices of each bank orientation can extend to
193 vertices (192 edges), using the unchanged baseline necessary-condition CNF
encoder. All additions are confined to `work/keep96/` and `outputs/keep96/`.
The independent clone and branch start at `acee575`; KEEP=112 files and workers
were not changed or run.

- Validated all 131 bank paths in both orientations: 262 positive controls at
  their correct 192-vertex witness length, including every auxiliary counter.
- Twelve structurally varied pilot entries: all solver UNSAT within 300 seconds
  each. A gated screen of the remaining 250 used ten seconds per entry.
- Combined: **242 solver UNSAT, 20 UNKNOWN timeouts**, no SAT constructions.
  Each worker had a hard 2048 MiB memory limit. The target was never weakened.
- Executable RUP audit: 21 certificates passed; three pilot certificates timed
  out at 60 seconds. Other certificates were not replayed. This is not Lean
  verification and does not establish the global optimum.

Includes resumable generation/solving, configuration and artifact hashes, all
262 compressed formulas with mappings and clause provenance, solver logs,
machine-readable tables, and a concise report. Small certificates are included;
large certificates are retained in the isolated local clone and indexed by
path, size, and SHA256. See `outputs/keep96/certificate-index.json` for availability.

Validation: five control tests passed; all saved evidence hashes and all DIMACS
versus mapping contents checked; pilot resumption reused all twelve completed
results without new solver calls. No changes under `work/lean112/` or
`outputs/lean112/`.

Start with `outputs/keep96/REPORT.md` and `work/keep96/README.md`. Full KEEP=96 Lean
formalization remains premature until UNKNOWN cases and certificate scalability
are addressed. This PR does not merge or modify the running KEEP=112 campaign.
