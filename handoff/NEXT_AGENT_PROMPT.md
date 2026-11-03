# Continue after milestone 147

Work in E:/Snake-in-a-box. Apply tensai-bishoujo with the user's formal
tone, no emojis and only necessary recurring definitions. Keep the existing
open paper D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex synchronized
with paper/snake9_research.tex. Preserve authors Iori Hironaka, Tommy Ma,
Steven Zhan and the complete preamble. Preserve unrelated .gitignore and
milestone50 critical-family changes. Goal ACTIVE; round147 made progress.
Last full paper revision146; next156. Compilation currently fails before TeX.

Read milestones/147-countfree-clause-semantics/MATHEMATICAL_NOTE.md and
data/checkpoint.json. Semantics113 modules complete,111 axiom reports:
all12977 original core clauses,102 clause modules,six acyclicity cuts.
Semantics147 proves Unsat implies RefutedShare; Unsat is still a premise.
The exact original input is unchanged. Do not repeat those checks.

The replay36-module pilot is complete. The first full32-segment group
also passes:47 accepted modules,8653 deductions,195344 references,complete
checkpoint transfer. The immutable boundary is in
replay/data/first-group-completion.json and first-group-progress-snapshot.json.
The full generated plan has1789 modules,5089segments,160groups and ends in
Unsat of the exact ShareWindow146 core. Every emitted proof literal and
checkpoint was independently compared with the saved packed data.

First inspect replay/data/full-replay-progress.json, its lock, current
processes and any work/live-replay147.json. A remaining full replay may
already be running. Continue the same process, never duplicate it.
If no process is active and the last run ended successfully, resume
scripts/run_full_replay.py; accepted receipts are revalidated and reused.
The script belongs under milestones/147-countfree-clause-semantics.
If a module failed, inspect its exact failure before any new attempt.
Do not mutate source plans, accepted source/object/log/checker snapshots,
or dependency pins. A layout change needs a separate preserved plan.

Lean4.19 rejects its advertised -M option. Use the external memory guard.
Current runners require zero other Lean processes,free>=1.5GiB at launch,
own private memory<=3GiB and free memory>=768MiB. Generic modules use
one thread and8192KiB stack; concrete modules use two threads and65536KiB.
Fullgraph also requires>=3GiBfree and no other fullgraph job.

After complete replay, audit the final Unsat theorem and compose it with
the checked local semantics, coordinate transport and reversal. No actual
share16 theorem exists yet. Keep012032 and012340 as joint dependencies.
The maintained191--235 interval uses the inspected contributor upper proof;
a full independent rebuild is pending. Conditional234 retains its premises.
The196 conjecture and optimum are unresolved. No new global bound in147.

The1397-module012310 count-sum proof is complete and must not be restarted.
The separate012034 share18 proof has a complete initial-tree bridge and
1055-deduction prefix; its remaining full replay is unfinished.

Large immutable replay inputs and all source modules are archived in147.
Use scripts/restore_archives.py to restore missing exact bytes on a fresh
checkout. Objects are local build outputs. See the publication manifest
for exact published files. Live full-replay progress is deliberately
outside the immutable publication boundary. Fetch each round, stage only
manifest files, commit quietly, push and verify remote. Preserve failures.
