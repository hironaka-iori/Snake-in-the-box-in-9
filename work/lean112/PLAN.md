# KEEP=112 continuation contract

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
