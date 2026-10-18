# KEEP=96 Lean completion campaign

This independent full clone starts at `a0dc85a113570d3fc7614cff879f25d492edf8de`
on `research/dfs-lean-completion`. Production branch:
`research/keep96-lean-completion`. The remote feasibility branch at `1dcf198`
was already merged; it had no additional commits. No applicable AGENTS.md was
found. Repository README and collaboration instructions were read.

## Exact objective and current evidence boundary

For each of 262 oriented entries from 131 bank paths, exclude every Q9 induced
path of at least 192 edges whose first 96 vertices match that orientation; also
prove the reversed-end and aggregate statements. The suffix begins at index 95,
has 97 edges and 98 vertices, and has 49 vertices of each parity. This is a
conditional bank-prefix exclusion, never a global optimality claim.

`outputs/lean96/progress.json` is the live record. Only an entry with a compiled
geometric bridge, kernel-checked Boolean contradiction, exact bank identity,
and standard-axiom audit counts. The status is not complete until final audits,
report and branch push have succeeded. A running campaign is not a theorem.

The remote survey supplies 187 complete certificates. Seventy-five certificates
are absent, including all 20 entries whose reported subsequent 300-second
results were not found on GitHub. Those reports are not counted. Missing evidence
is regenerated with Glucose 4.1 / python-sat 1.9.dev16, default parameters, proof
logging, a 300-second wall limit and 2048 MiB. Original attempts are preserved.
SAT in the relaxation is not a mathematical counterexample or a snake.

## Proof method

The unchanged `work/build_regrowth_cnf.py` is called with `keep=96` and
`total_vertices=193`. Inventory checks all saved formulas against this encoder.
The 98 proposed representative regions cover all entries via cube translations
and inclusions. Every inclusion, translated head and bank-prefix identity is a
separate Lean obligation, not a trusted Python inference.

The generic KEEP=112 bridge is adapted into the separate `Snake9.Regrowth96`
namespace with the correct numerical suffix and parity counts. Selection and
endpoint variables denote path properties; totalizer wires denote thresholds
of counts of signed leaves. Every input clause retained by the certificate is
proved from geometry, including selected/absent parity bounds and the unique
other endpoint. Unused CNF clauses are unnecessary: contradiction from this
geometrically justified subset suffices. The full encoder need not exclude
disconnected cycles in arbitrary satisfying models.

Native DRAT-trim verifies proofs and emits LRAT hints; Python trims the dependency
core. Neither is trusted by Lean. `LocalRup.lean` and `TreeRup.lean` prove the
soundness of inference checks; generated modules use ordinary kernel-reduced
`decide`. The final audit permits only `propext`, `Classical.choice`, `Quot.sound`.
No admitted proof, custom axiom or native decision shortcut is allowed.

KEEP=112 and KEEP=144 sources/evidence remain unchanged. Existing standard-library
dependencies are rebuilt into the separate `outputs/lean96/cache/`, without
reusing the other campaign's compiled files.

## Reproduce and resume on Windows

Use Python 3.12 and Lean 4.19.0. Set `LEAN96_LEAN` to the absolute Lean executable
if different from the local default recorded in `runner.py`.

```powershell
python -X utf8 -m pip install --only-binary=:all: --target work/lean96/.packages python-sat==1.9.dev16 psutil==7.2.2 six==1.17.0 ziglang==0.13.0
python -X utf8 work/lean96/inventory.py
python -X utf8 work/lean96/runner.py --workers 1 --representatives 118
powershell -File work/lean96/start.ps1 -Workers 3
```

Run inventory only before starting or after stopping the runner. The standalone
runner holds a Windows OS file lock, including setup, so duplicate launches exit.
Launch scripts use hidden windows. The read-only dashboard is
http://127.0.0.1:52096/ and checks both runner PID and creation time. A dead worker
is shown as stopped unexpectedly; a persistent process alone is not completion.
The separate `campaign.py` controller also has a process lock. It waits for an
already running representative job, requires entry 118 and its complete
representative audit to pass, saves `representative-gate.json`, and only then
starts the three-worker full queue. A first-entry failure stops scaling and is
left for the continuation check. The controller remains independent of chat.

Default limits: three compilation streams, one serialized evidence preparation
stream, 4096 MiB and 1800 seconds per Lean/native check. The foundational Snake9
module has a separately recorded 12288 MiB cap and runs sequentially with one
Lean thread; its first 4096 MiB attempt ran out of memory. Core trimming is capped
at 6144 MiB / 1800 seconds. Native checker sources are the existing unmodified
DRAT-trim snapshot, compiled with Zig 0.13.0; build flags and binary hashes are
recorded. Current throughput is not sufficient for a reliable whole-bank ETA.

Every successful module saves source, direct dependency, compiler, compiled
artifact and log hashes, elapsed time and resource limits. Resumption validates
identities and does not silently reuse missing evidence. Each failed attempt
keeps its log; evidence attempts use unique directories. A failure stops that
group while independent groups proceed. An unresolved group is not automatically
retried; after a concrete repair, use `--retry-failures` with a bounded set of
`--representatives`. Never edit sources currently being compiled. A changed
failed method should be tested on one group before restarting the full queue.

The Codex thread heartbeat `keep96-lean-continuation` runs approximately every
30 minutes to investigate actionable failures and finish packaging. It leaves
healthy workers alone and is quiet during ordinary progress. The standalone
runner does not depend on the chat for queued compilation, but cannot invent
mathematical repairs on its own. Scheduling depends on the app/host being
available. After shutdown, rerun the launch script to resume from saved work.

## Artifacts and final packaging

### Resource repair checkpoint (17 October 2026)

The first representative and its region-reuse entries passed; the initial batch
then completed 11 entries / 3 representatives before stopping with resource
failures. Large monolithic Boolean input modules exhausted allocation or failed
to create threads. Input proof declarations are now split into modules of 32
clauses, and Lean explicitly uses a 16384-KiB thread stack. The entry-246 pilot
checks the changed method before a two-worker retry. Launch that guarded
continuation with `work/lean96/start.ps1 -Workers 2 -AfterRepair`; it waits for
the pilot to stop and requires its complete theorem and axiom audit to pass.
No identical failed full-bank run is automatically repeated.

Entry 256's trimming failure occurred while building a huge JSON string after
the mathematical trimming computation. `trim_worker.py` now streams compact
JSON to an atomic temporary file. Successful earlier solver attempts are reused
only after formula, encoder and certificate hashes match. Original attempts and
failure logs are retained. These repairs do not change the target or axioms.

Large raw DRUP/LRAT certificates, decompressed formulas and compiled objects are
local-only under `outputs/lean96/artifacts/` and `outputs/lean96/cache/`. Each
prepared entry has `cores/entryNNN.receipt.json` with exact paths and SHA256
hashes. The solver configuration is stored in its unique attempt directory.
Generated Lean sources, appropriately sized receipts and logs will be committed;
large cores can be regenerated by the same runner from the pinned formula and
solver, followed by native LRAT generation and `trim_worker.py`. A fresh clone
does not contain omitted artifacts and must regenerate them rather than trusting
historical completion receipts. No success is claimed from missing objects.

Final verification must check all 262 entry audits, all representative bridges,
the four `Snake9.Regrowth96.Bank96` aggregate statements, all source/dependency/
object hashes, and preserved certificate hashes. After success, produce an
English results report, push only `research/keep96-lean-completion`, mark the
dashboard complete, and disable the continuation heartbeat. Do not merge.

### Second resource repair (18 October 2026)

The bounded batch stopped with 83 audited entries / 24 representatives.
Derived RUP modules of 64 steps still exceeded the 4096-MiB process limit
on many entries. New derived modules contain eight steps; the mathematical
inference checker and target are unchanged. Entry 179 is the new full-proof
validation gate before a two-worker retry. Original logs remain available.
Atomic JSON publication now uses unique temporary files and up to ten bounded
retries for transient Windows replacement conflicts (2.25 seconds total delay).
Failed writes remain failures; no completion is inferred from them.
