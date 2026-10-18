# KEEP=112 continuation contract

## Completed (2026-10-17)

All 262 entries, all 86 representatives, and the final `Bank112Results`
aggregate passed. The four aggregate axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. See `RESULTS.md` and the saved final
audit receipt. The continuation instructions below describe the historical
build workflow; do not restart a completed campaign without a new request.

## Current implementation (2026-10-16)

The first full geometric entry is PASSED, audited and pushed in commit
37a5d1e. `First112Complete.lean` proves exclusion of 192 and all longer
edge lengths for the fixed 112-vertex prefix. Its immutable completion
receipt is `outputs/lean112/first-geometric-proof.json`.

`run_bank.py` now generates and checks actual Boolean proofs, geometry,
translation inclusions and bank-indexed exclusion theorems. It holds
`bank-runner.lock`, saves `bank-module-checks.json` after every module,
and saves `bank-proof.json` after every complete entry. Check the PID in
`bank-runner.json` before doing anything. Never launch a duplicate runner,
modify a source while its compiler is using it, or overwrite its status.
The old dashboard service is separate and must remain on port 51993.

There are 86 proposed representative regions, using cube translations
and containment to cover 262 entries. `cover.json` is untrusted input;
each containment and prefix identity is separately checked by Lean.
The representatives require 255165 retained Boolean inference steps.
`LocalRup.lean` and `TreeRup.lean` prove the soundness of the small RUP
checks; the generated certificates are reduced by the Lean kernel.
`generate_bank_bridge.py` emits explicit geometry and count semantics.
Only final `Bank112EntryNNN` declarations passing an axiom audit count.

If the runner is active and making progress, leave it running quietly.
If a group fails, inspect its exact error in `bank-proof.json` and
`bank-logs/`, finish any missing Lean proof, and resume the runner after
its lock is released. Successful modules are reused against source,
artifact and direct-import hashes. The final aggregate `Bank112Results`
is required before declaring the 112 stage complete. After all checks,
document and commit/push on the existing research branch and disable the
heartbeat. Do not imply that completing this stage solves the global
nine-dimensional snake problem.

Normal launch: run `start-bank.ps1`. A terminal-only targeted repair can
use `python work/lean112/run_bank.py --workers 2 --representatives N ...`
after confirming that no runner is alive. A targeted run does not complete
the whole stage unless all 262 entries and the aggregate pass.

## Earlier stage context

The user authorized continued proof work, background execution and a live
monitor. Work only in this checkout, on research/dfs-lean-completion. Do not
alter main or claim global optimality. Do not spawn agents unless separately
authorized. Preserve the completed KEEP=144 evidence.

The local service.py runs two resumable tasks: the first Boolean certificate
and a bounded SAT survey of all 262 oriented entries. It serves dashboard.html
on localhost; outputs/lean112/server.json records the actual URL and process.
Every completed module and survey entry is saved atomically and recorded in
events.jsonl. Cached Lean artifacts are reused only against recorded source
hashes, with a fresh final import/axiom audit. Solver UNSAT is explicitly not a
geometric exclusion theorem. A SAT relaxation is not a longer snake.

The unfinished reasoning work is the geometric bridge and scaling the complete
formal proof to all entries. Continue this during authorized heartbeat runs:

1. Read outputs/lean112/first-certificate.json, survey.json, reasoning.json and
   recent events. Check service liveness without starting duplicate workers.
2. Prove generic necessary-condition and counter lemmas for an 82-vertex suffix
   of a hypothetical 192-edge snake sharing 112 fixed vertices. Reuse existing
   DfsCertificate, DfsDecide, DfsPrefix, PathStructure and BallClauseLogic.
3. Connect exact CNF clauses to the geometric path, including region coverage,
   degree, endpoints, parity counts, square exclusions and all counter wires.
   Formula identity must be checked before reusing any LRAT/Lean certificate.
4. Finish a full first-instance geometric exclusion. Then prioritize hard or
   structurally distinct survey entries; strengthen SAT relaxations where
   necessary. Generate and kernel-check remaining certificates with bounded
   memory. No sorry, native_decide, unchecked axioms or weakened goal.
5. Update reasoning.json atomically with status (PENDING, IN_PROGRESS, BLOCKED,
   COMPLETE), detail, updated_utc, formally_certified_entries (only final
   geometric Lean theorems count), and total_entries=262. Add proof details and
   remaining obligations here as needed. Keep the dashboard honest.
6. Save useful progress each run. All 262 entries plus an aggregate theorem,
   fresh allowed-axiom audit and documentation are needed for completion. Keep
   commits/pushes on the existing research branch; never merge main. Do not
   silently broaden to solving the global optimum.

The service completing its two initial jobs does not complete this task.
Keep mathematical continuation separate from the bounded computer jobs.
If a worker fails, inspect its saved error before restarting the service; never
launch a second instance while the service lock is held. The 112 target still
has substantial unproved obligations and no reliable overall percentage.
