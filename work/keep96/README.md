# KEEP=96 feasibility (isolated experiment)

Baseline: `acee575f181b8a6d35775f985169ec15cb2cf021`, fetched from
`research/dfs-lean-completion`. Work branch: `research/keep96-feasibility`.
Independent full clone: `E:/codex-research/keep96-feasibility`; no shared checkout,
linked worktree, object alternates, or synchronized active KEEP=112 directory.
No applicable AGENTS.md was found in the repository or its local parent directories.
The repository README was read. Only `work/keep96/` and `outputs/keep96/` are changed.
KEEP=112 worker scripts are not imported, executed, or edited.

## Encoding and evidence boundary

The unchanged baseline `work/build_regrowth_cnf.py` supplies the encoder. For a
prefix of 96 vertices, the head is vertex index 95. Closed neighborhoods of the
first 95 vertices are forbidden to all **new** vertices. The head is retained
explicitly; all remaining candidates must be reachable from it through allowed
vertices. A genuine extension necessarily lies in this region.

For each region vertex `v`, `selected[v]` indicates selection and `endpoints[v]`
indicates degree one. Local clauses enforce selected degree one or two, endpoint
degree exactly one, and that every degree-one selected vertex is an endpoint.
The head is selected and an endpoint; exactly one other endpoint is required.
Parity clauses restrict that other endpoint to the target path parity class.
Four-cycle clauses forbid fully selected coordinate squares.

The target selected region size **includes the head**:
`total_vertices - keep + 1`. For the actual question it is `193 - 96 + 1 = 98`
(49 vertices per parity). The known bank witnesses have 192 vertices, so their
positive-control size is `192 - 96 + 1 = 97`. The positive controls deliberately
use the witness length; the experiment never substitutes that weaker target.

Counter wires have the intended witness meaning: output `k` is true iff at least
`k` signed leaves are true. The tree encoding only imposes forward implications;
arbitrary satisfying assignments need not set every counter to this canonical
meaning. Forward implications plus the bounded output suffice for the at-most
constraint. Applying at-most to selected literals and to their negations enforces
exact parity counts. For a genuine path, canonical counts provide values for
**all** auxiliary wires satisfying these implications. Positive controls check
every clause and every wire, including negative absent-count leaves.

There is no full connectivity/acyclicity constraint. A satisfying model may be a
head-to-end path together with disconnected induced cycles of length at least six.
SAT therefore is not a 192-edge construction. Every SAT model is checked against
all CNF clauses, decomposed, and its head path reconstructed with the fixed prefix.
Any reported snake is checked over every unordered pair, including distinctness,
consecutive adjacency and forbidden nonconsecutive adjacency.

UNSAT is a solver result for these necessary conditions, not a completed Lean
proof. An executable RUP replay, if present, is also not Lean verification.
Timeouts/errors/memory termination remain UNKNOWN. Prefix exclusions are not a
global upper bound for arbitrary nine-dimensional snakes.

## Setup and reproduce

Python 3.12, with packages isolated to this directory (not committed):

```powershell
python -m pip install --only-binary=:all: --target work/keep96/.packages -r work/keep96/requirements.txt
python work/keep96/prepare.py
python work/keep96/test_controls.py
python work/keep96/run.py --phase pilot --seconds 300 --memory-mib 2048
```

`prepare.py` checks 131 bank paths in both orientations (262 entries), each a
191-edge induced path. The unchanged witness is also checked to fail the 193-vertex
target. Selection is deterministic, outcome-blind farthest-point sampling on eight
min-max normalized structural features: region vertices/edges, head degree, degree
one/two counts, parity imbalance, squared prefix coordinate counts, and prefix
endpoint Hamming distance. Start at the largest forward region, alternate
orientations, disallow duplicate bank indices, break ties by smallest entry.
All 262 feature vectors and the chosen 12 are saved in `pilot-selection.json`.

Solver: Glucose 4.1 (`g4`) through pinned python-sat, proof logging on, otherwise
default parameters (no custom seed, incremental mode, or extra clauses). The solver
extension binary SHA256, package/Python/platform versions, source hashes and full
configuration are saved. The parent enforces **300 seconds per worker**, including
startup, solving and evidence serialization. Poll interval is 0.1 seconds. Windows
workers use a hard 2048 MiB per-process committed-memory limit via a Job Object;
the parent additionally watches RSS. On POSIX the worker uses RLIMIT_AS. A worker
failure that cannot be distinguished from an allocation failure is conservatively
reported UNKNOWN with `WORKER_ERROR_OR_MEMORY_LIMIT`, never UNSAT.

Each formula is preserved as deterministic gzip DIMACS and full JSON containing
clauses, variable mappings, counter semantics, prefix/banned region and per-clause
provenance. Each attempt has its own timestamped directory, start record, solver
log, final result, hashes and available model/DRUP certificate. Finished results
are saved after each entry. The JSON and CSV summary are machine-readable.

## Resume and scale

Rerun the same command to resume. Reuse requires identical formula/configuration
identity and matching artifact hashes. Completed SAT/UNSAT records are reused.
UNKNOWN attempts are retained and skipped by default; `--retry-unknown` explicitly
requests another bounded attempt. An interrupted attempt with only `started.json`
is not a completed result and cannot be reused. Different limits/code/formulas
produce a different identity directory. Never run two drivers for the same phase
at the same time. Preserve the repository's baseline bank and encoder.

The recorded pilot passed the explicit scaling gate (at least nine UNSAT, at
least six under ten seconds). The remaining 250 entries were screened once with
a ten-second worker limit; the mathematical target stayed at 193 vertices.
Reproduce that decision and the final evidence audit with:

```powershell
python work/keep96/screen_remaining.py
python work/keep96/audit_results.py --phase pilot
python work/keep96/sample_proof_checks.py
python work/keep96/finalize.py
```

The survey proof audit samples twelve UNSAT runtime rank quantiles; it is not an
audit of every certificate. Each replay has a sixty-second limit. There is no
automatic escalation or unbounded search. The final combined table records both
budgets separately. Full certificates remain in the original isolated clone;
Git includes only certificates at most one MiB each, with a combined twenty MiB
budget. `outputs/keep96/certificate-index.json` identifies every omitted proof by
path and hash. Transfer omitted proofs from the original clone, or rerun their
recorded configurations. A fresh checkout cannot reuse missing proof artifacts.

For a saved UNSAT attempt, an optional executable RUP replay is:

```powershell
python work/keep96/check_proof.py outputs/keep96/runs/ENTRY/CONFIG/ATTEMPT
```

Run proof replay in a supervising process with a timeout (60 seconds for this
investigation). It also applies the 2 GiB memory cap. Non-RUP steps are rejected;
deletions may be ignored because all retained learned clauses were justified.
Empty proof output is accepted only if original clauses have a unit-propagation
contradiction. No Lean campaigns are launched by any of these commands.
