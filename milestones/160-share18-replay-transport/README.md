# Completed prefix checkpoint

The prefix transport and all three checkpoint modules passed. Read
COMPLETION.md and data/completion.json. The remaining full contradiction
and actual-snake theorem are unfinished. The preparation description below
is historical and its execution instructions should not be repeated.

# Milestone160: accepted-prefix transport and checkpoint

Status: sources prepared; the transport has not run. No solver, compiler, proof allocation, unit-propagation replay or native resource snapshot was started during preparation. Milestone159's semantic batch must be terminal before execution.

This bounded experiment preserves the existing144 share18 input and checks the first1,055 deductions, containing6,006 propagation references. Its output is a materialized checkpoint and three Lean sources for connecting the accepted prefix to that checkpoint. It does not generate or replay the remaining full proof.

## Exact scope

The worker checks the compact13,224-clause CNF against the original clause IDs and the saved6,371-variable map. The compact proof already uses the renamed variables and compact input IDs. It is read unchanged; no second renaming occurs. The5,779 active proof variables, offset8,192,14-bit words and depth14 tree remain fixed.

Two streaming passes over the existing105,893,029-byte compact LRAT reproduce the original allocator. They count145,215 deductions and14,710,881 references, preserve the original frequency/tie ordering and lifetime rules, and require exactly14,114 slots. These passes gather allocation information; only the first1,055 deductions undergo unit-propagation checking. Full proof checking remains a later task.

Every prefix destination and hint slot is transported through the exact preorder map. All1,055 packed integers must equal the accepted `LiteralProbe144.proof` values. Any mismatch stops the run. The checkpoint retains clauses still needed after the prefix and replaces other entries by the checker's tautology marker. An independent decode checks every nonzero checkpoint entry against the resulting prefix database. This is the correspondence required by `cpOk`: retained entries agree and discarded entries become tautologies. Equality of the complete databases is neither required nor claimed. The Lean check of this correspondence remains pending.

The future output under `data/prefix1055/lean/` consists of:

- `CheckpointData160.lean`: the16,383 checkpoint entries and their depth14 tree.
- `CheckpointCheck160.lean`: the proposed kernel check of `cpOk` between the accepted prefix replay and the checkpoint.
- `CheckpointConsequence160.lean`: composition with `PrefixAssoc146.checked_prefix_true` using the existing `cpOk_true` theorem.

The combined Lean source size is capped at8MiB before any source is written. These files will be uncompiled. A successful Python receipt explicitly states that the Lean checkpoint, complete share18 replay and actual-snake theorem remain unchecked.

## Execution gates

`run_prefix.py` requires milestone159's original semantic progress and, when present, its final-batch progress to be terminal, with no active module. Either `semantic-batch.lock` or `semantic-final-batch.lock` blocks launch. Both progress hashes are captured in the execution request and rechecked by the worker; the absence of final progress is also preserved when applicable. The runner additionally requires zero Lean processes and zero recognized graph processes. It checks this state throughout the run, so a gap between159 compiler invocations is insufficient to pass the gate.

The runner permits one transport worker, monitors combined parent/worker private memory against1GiB, requires1.5GiB free before launch and768MiB during execution, and stops after180seconds. Memory is sampled every0.2seconds through the copied native Windows helper; this is a monitored threshold, not an operating-system allocation cap. Query failures or a restarted159 batch stop the worker. Earlier run folders and lock evidence are preserved; the runner removes only its own lock when it exits normally or handles a failure.

Both runner and worker retry JSON reads and atomic file replacement on `PermissionError`, with at most40 attempts separated by50milliseconds. Other errors still stop the run. The resource helper and guard are byte-identical copies from155 and157 and make no CIM calls. Source preparation pins five scripts and31 input entries, including the exact proof, accepted prefix source/object/log,146 prefix consequence, and the relevant generator and checker sources.

## Future command

From `E:\Snake-in-a-box`, after milestone159 is terminal:

```powershell
& 'C:\Users\hironakaiori\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' -B -X utf8 'milestones/160-share18-replay-transport/scripts/run_prefix.py' --label prefix1055
```

This command has not been run. A successful result will be recorded in `data/prefix1055/prefix-transport.json`, with source and checkpoint hashes, exact prefix totals and the three-module order. The next step would be checking those three generated modules with pinned144/145/146 dependencies. Full replay emission remains a separate task after that checkpoint check succeeds.

`scripts/prepare_sources.py` reproduces the source plan using file hashes and Python syntax checks only. It refuses to replace a changed plan. It does not invoke the transport worker or query running processes. Superseded source plans from preparation are preserved beside the current plan. All144–159 sources, objects and evidence remain unchanged.
