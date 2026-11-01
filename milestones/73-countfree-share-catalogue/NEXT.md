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

## Next local certificate

After completing any active case, prioritize **case 7305**, shape **012310**,
with share lower bound **12**. Its selected native certificate is
`general5-cap11-certificate.json` in milestone72/critical-current. Do not substitute
the much larger uniform-share-16 experiment for this mixed-catalogue requirement.

The reason for this priority is structural. The already checked distinct-direction
share-12 theorem covers 012345. Case7306 targets 012314. Adding a positive share
for 012310 completes one of the four minimal covers of the original mean-480
critical family, recorded in milestone72's `critical-current/data/shape-cover.json`.
Recompute the finite model after discharging the premise; a removed old critical
cycle alone is not a global improvement.

The case pipeline is:

1. `scripts/bootstrap_case.py 5`.
2. The new case's `scripts/prepare_lean.py`, then `scripts/assemble.py`.
3. `scripts/add_reversal.py 7305`, `scripts/generate_lrat.py 7305`, then
   `scripts/export_lrat.py 7305`.
4. The case's `scripts/replay_share.py`, then `scripts/complete_share.py`.
   A separate `--lrat-only` pass may run alongside semantics, followed by one full
   completion pass after both finish. Keep memory use bounded.
5. The case's `scripts/audit_share.py`, followed by `scripts/archive.py 7305` and
   `scripts/restore.py 7305`.
6. `scripts/check_integration.py`, `scripts/checkpoint.py`, and
   `scripts/evaluate_checked.py`.

The proof audit must cover the arbitrary-snake geometry and reversal, in addition
to all Boolean proof modules. `check_integration.py` inserts completed refutations
into the generic canonical adapter and the partial catalogue theorem.

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

The paper is still revision66; the next full rewrite is scheduled for milestone76.
Its repository source and the existing D: editor source have matching hashes.
Preserve Iori Hironaka, Tommy Ma and Steven Zhan as authors and preserve the local
hyperlink settings. Write the eventual paper in mathematical notation and arguments;
Lean filenames and implementation definitions must not replace its mathematical
statements. Keep unproved catalogue premises explicit. The research goal remains active. No new optimality claim,
196-edge witness, or unconditional234 theorem is supplied by this checkpoint.
