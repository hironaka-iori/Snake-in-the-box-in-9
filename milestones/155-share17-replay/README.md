# Share-17 contradiction replay

Status: source prepared; no Lean or solver invocation.

This milestone checks the single contradiction shared by the exact-count and
broader-interval share-17 models. Its 34 pilot modules are byte-identical copies
of the immutable milestone153 pilot. The broader clause semantics and actual
snake transport belong to milestone154.

The pilot covers the complete initial clause tree, then 2,095 deductions and
6,002 propagation references, including the full resulting checkpoint. Its
acceptance does not establish the complete contradiction. The full numerical
replay contains 30,305 deductions and 1,754,767 references; the complete Lean
replay is expected to have 137 modules including the pilot.

## Dependencies and execution

The shared CNF must first have an accepted receipt at
`154-share17-broader-semantics/data/LocalWindowCnf.ShareWindow153-audit.json`
and its matching object in `154-share17-broader-semantics/build`. Generic
local models come from milestone147 with their existing receipts.

After the current compiler batch has finished, run from the repository root:

```powershell
python -B -X utf8 milestones/155-share17-replay/scripts/run_replay.py
python -B -X utf8 milestones/155-share17-replay/scripts/finish_pilot.py
```

Use the configured Python executable if `python` does not resolve to the project
runtime. `SNAKE_LEAN_BIN` may identify another local Lean 4.19.0 installation;
the checker records and pins the actual compiler. Its default is the existing
project installation.

`run_replay.py --limit N` checks at most N new modules while revalidating earlier
accepted receipts. A complete run uses no limit. A stale lock is evidence to
inspect; do not delete it or restart a driver without checking its process.

The checker requires no other Lean process and at least 1.5 GiB free memory.
It stops its own compiler at a 3 GiB private-memory limit, below 768 MiB free
memory, on a conflicting compiler, or on the per-module timeout. The default
timeout is 180 seconds. Generic modules use one thread and an 8,192 KiB stack;
concrete modules use two threads and a 65,536 KiB stack.

Acceptance requires exact source, object, log, checker, and dependency hashes,
successful compiler termination, all requested axiom reports, and only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Copied sources
remain pinned to the original milestone153 bytes. The accepted pilot receipt
is `data/pilot-completion.json`.

## Full replay after pilot acceptance

The prepared adaptation reads the packed inputs from milestone153 and writes
only this milestone. It first reruns the saved-evidence pilot auditor and
refuses generation until the pilot is complete:

```powershell
python -B -X utf8 milestones/155-share17-replay/scripts/emit_full.py --full --max-source-mib 256
```

It preserves the existing 34 sources and writes the additional full-replay
sources plus `data/full-source-plan.json`. It never launches Lean. The original
milestone153 emitter and metadata remain unchanged.

Before executing those full sources, prepare a separate full checker and
runner from the pilot scripts: use `full-source-plan.json`, pin its generator
and accepted pilot receipt, and use distinct `full-replay-progress.json` and
`full-replay-batch.lock` files. Validate and reuse the existing accepted pilot
receipts with their saved pilot checker rather than recompiling them or
requiring their checker hash to equal the new full checker. Use the same
`build` directory, so every existing module is reused by its original name.
The full checker must permit module names containing underscores.

After the final shared-CNF contradiction is checked, compose it with the
milestone154 actual-snake implication in a separate checked module. No stronger
global upper bound is established by the pilot or by this prepared execution
package.
