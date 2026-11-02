# Continuation record

The exact Q9 optimum remains unresolved. Length is measured in edges. The project
interval is **191 <= a(9) <= 235**; **234 remains conditional**. Read
`data/checkpoint.json` for the completed local cases and `data/integration-audit.json`
for the certificate premises still present in the combined theorem. A generated
source or a native UNSAT certificate alone is insufficient to mark a case complete.

## Resume a running proof before starting another

Check the case's `logs/semantic-record.json`, `logs/composition-record.json` and
`logs/completion-record.json`, together with its active process. An observation
timeout does not mean the Lean process failed. Never run two completion processes
for the same case concurrently. The completion driver resumes source-matched
successful modules. Its final source/axiom audit must pass before archiving.

Every proof is retained as sources, compact CNF/LRAT, compiler logs and hashes.
`scripts/restore.py CASE` restores missing archived files and rejects conflicting
existing bytes. The native certificate inputs remain in milestone72's
`critical-current/certificates`; use that task's restoration script when needed.
The inherited support builds are required by the current replay scripts.

The current Windows runtime paths are:

- Python: `C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
- Lean 4.19.0: `D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin`.
- Pinned mathlib: the `mathlib` directory beside that Lean installation.

Use `E:/Snake-in-a-box` as the working repository. No package installation is
needed for the saved Lean replay. Inspect script paths before using another host.

## Current local certificate: case 7302

Milestone 80 completed case7305, including all465 modules, geometry, reversal,
100 theorem audits and archive restoration. Do not restart that completed
case. The remaining target cases are7301,7302,7303,7307,7308.

Milestone 83 is now checking **case7302**, direction shape **012034**, with
share lower bound **20**. Its selected native input is
`pysat2-cap19-certificate.json`; it has universal bounds[0,21] on all five
internal counts and no cycle cuts. The semantic and compact-proof work is
under `cases/case7302/`; current process observations and the conditional
comparison are saved in `../83-012034-share-certificate/`.

The choice follows milestone82: the current mean483 cycle contains the
012034 target twice and the012340 target once. Applying only the unproved
012034 floor20 gives exact conditional finite mean9259/19 and integer
comparison235. A local theorem still requires all replay and geometric gates.

For a new case the pipeline is:

1. `scripts/bootstrap_case.py INDEX`, once, before any source checks.
2. The case's `scripts/prepare_lean.py`, then `scripts/assemble.py`.
3. `scripts/add_reversal.py NUMBER`, `scripts/generate_lrat.py NUMBER`, then
   `scripts/export_lrat.py NUMBER`.
4. The case's `scripts/replay_share.py`, then `scripts/complete_share.py`.
   The semantic and LRAT stages may be run separately with the documented
   options, followed by one complete assembly pass. Inspect current processes
   first and never duplicate a running driver.
5. The case's `scripts/audit_share.py`, then `scripts/archive.py NUMBER` and
   `scripts/restore.py NUMBER` after the final local theorem passes.
6. `scripts/check_integration.py`, `scripts/checkpoint.py`, and
   `scripts/evaluate_checked.py` after admitting the completed case.

Case7302 has already been bootstrapped. Reuse its generated source and
source-matched successful checks. The case-specific slicing adaptation in
milestone83 preserves the original compact proof and requires independent
simulation before selecting a smaller proof. It does not change the input
clauses. Selection must follow its process and source-integrity guards.

The final audit must cover arbitrary-snake geometry and reversal, in addition
to every Boolean proof module. A generated source, native refutation or
partial replay must not be added to the completed catalogue.

## Conditional and proof-supported comparisons

The full mixed catalogue has exact finite mean 496 and potential range 600. Its
conditional arithmetic excludes 235 by a margin of 32. The nine required shares
are 20 for 012034, 12 for 012310, and 16 for the other representatives. The fixed
potential audit `data/required-shares.json` shows that none can be lowered while
keeping that graph and potential and adding no alternative rules. This is a
restricted minimality result, not a claim about all possible proofs.

`scripts/evaluate_checked.py` adds only completed local share theorems to the
audited ten-count/share-120 model. Its optional argument
`--assume=012310:12` creates a separately labelled conditional comparison. It must
never be reported as a proved local premise. Both calculations verify every edge
of their finite model and an attaining cycle; their snake interpretation and Lean
potential replay remain separate obligations.

## Global assembly

These pieces are checked and reusable:

- The actual-snake nine-shape coverage theorem in `coverage/`.
- The canonical coordinate and reversal adapter in `adapter/`.
- The conditional nine-certificate catalogue dispatch in `adapter/`.
- The equality of local certificate shares with global square shares, and the
  generic five-centre overlap budget, in `bridge/`.
- The earlier boundary lemmas, traced in `bridge/data/accounting-audit.json`.

The graph edge beginning at r uses entering count `min(6,alpha[r+8])` and share
centres r+4 through r+8. Window starts satisfy r<m-8. Counts omitted from the
entering-count sum are 0 through 7 and m, with total at least 21 for m>=8.
Same-centre alternative credits combine by maximum. The value6 is a truncated
bucket covering actual counts6 through21, not an exact count.

Still required: construct the arbitrary-snake walk in the exact graph; justify
each count restriction, history transition and local share lookup; match all
indices to the budget; and apply the exact potential with its endpoint correction.
Do not infer these steps from a successful import or a numerical all-edge check.

## Preservation

Keep exact proof bytes through the task's `.gitattributes` and run
`scripts/check_staged.py` after staging. Stage only this task and deliberate
documentation changes; unrelated working changes are present in the repository.

The paper is revision76; the next full rewrite is scheduled for milestone86.
Its repository source and the existing D: editor source have matching hashes.
Preserve Iori Hironaka, Tommy Ma and Steven Zhan as authors and preserve the local
hyperlink settings. Write the eventual paper in mathematical notation and arguments;
Lean filenames and implementation definitions must not replace its mathematical
statements. Keep unproved catalogue premises explicit. The research goal remains active. No new optimality claim,
196-edge witness, or unconditional234 theorem is supplied by this checkpoint.
