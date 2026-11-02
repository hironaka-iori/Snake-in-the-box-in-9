# Resume the complete batch

1. Read `data/batch-progress.json`, `data/plan.json`, and the most recent batch
   log. Inspect `data/batch.lock` and `data/check.lock`, and verify whether their
   recorded processes are alive. A running batch should be allowed to continue.
2. If the batch stopped with an ordinary Lean error, inspect its exact source
   snapshot and log. Preserve them. Repair only the inactive failed source and
   deliberately update the proposed plan and source hashes if needed; do not
   rewrite any successful audited source.
3. If both variants of a group time out, preserve both attempts. That context
   remains unresolved. Split its code interval or prefix into smaller checked
   pieces before resuming; a timeout is not a mathematical counterexample.
4. Resume with `scripts/run_batch.py` only when no batch is active. The driver
   validates previous receipts and skips successful groups. It runs the two
   final graph assemblies after all groups pass.
5. After successful assemblies, audit every selected source, compiled object,
   dependency hash, log, axiom report and context key. Save the final coverage
   and exact manifest, update the shared handover, commit and push. Do not mark
   the research goal complete: the local refutations and optimum remain open.

The initial `GraphAssembly104` attempt needed an explicit predicate argument
to the list-search lemma. The corrected source passed. An early invocation
also named two groups that the generator correctly omitted because their
contexts were already checked. It stopped on the missing file before any
finite certificate was attempted; the run record is preserved.

Do not rerun `prepare.py` over the active environment. Do not regenerate the
entire source set during the batch. The 2,314 generated files include both
variants for 1,157 groups; their existence alone supplies no proof.

The original case7302 target 20 replay remains stopped and unchanged. A target
18 proof needs separate files. Preserve the reference catalogues and the
pending conditional caps (15,17,15,15,15), which would give share floors
(16,18,16,16,16).
