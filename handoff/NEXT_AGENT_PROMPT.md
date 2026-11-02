# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
100's mathematical note, checkpoint and proof summary. The previous turn made
progress: two complete graph contexts now pass Lean, through a checked prefix
traversal and exact context specialization. The active goal remains unresolved.

## Next task

Generate constant data and emitted history-rule lists for the remaining
contexts. Prove each specialization once, then use PrefixChecker100 with the
simplified leaf inequality and transfer it to the original contextCheck.
The generic historyCredit_filter_emitting theorem preserves all active rules
and their order. The short-history theorem removes the history contribution
when the stored prefix has fewer than two symbols. Fixed longer histories
can also emit no rule, as shown by the checked context 177/43 example.

Reuse these completed context theorems:

- ReducedCompleted100.completed_context_reduced: completed profile, slope 483,
  direction 35/history 0, all 7,151 accepted edges.
- ReducedConditional100.conditional_context_reduced: conditional profile,
  slope 496, direction 177/history 43, all 6,598 accepted edges.

Both are in namespace Snake9.PrefixCertificates100. PrefixChecker100 proves
contextCheck_of_prefix for arbitrary weights and potentials. ContextEndpoints100
and WeightSpecialization100 show how exact all-code equations transport a
small arithmetic check back to the original graph. Preserve source/history/
count keys, source/target order and raw state numbering.

The older CompletedContext100 and ConditionalContext100 sources are superseded
benchmark implementations. The former reached 300 seconds; the latter was not
started. Do not blindly restart them. If a new whole-context check is too
large, prove its six first-symbol branches separately and assemble them using
the same prefix recursion. Bound each trial and retain exact failed attempts.

Numerical classification gives 582 joint groups among 791 contexts, but these
groups need Lean equality and transport statements before certificate reuse.
Acceptance classes or endpoint pairs alone do not identify the weight.
One complete context per profile is proved so far; all-context certification
remains pending. The older 207 pilot edges lie inside the completed contexts.

## Global evidence and remaining assumptions

The maintained interval is $191\le a(9)\le235$ edges. The upper bound uses
the inspected contributor theorem and archived audit; a complete independent
rebuild remains pending. The improvement to 234 is conditional. No 196 witness
or optimality proof has been obtained.

Both potential arrays pass every one of the 4,947,008 defined graph edges in
independent exact-integer enumeration. There are zero extra/missing keys.
Both concrete potential range bounds are Lean-checked: 551 for completed,
602 for conditional floor 18. Completed slope is 483; conditional slope is 496.
The actual weight, boundary saving, total charge and full-key walk are checked
in milestone 98. Complete finite edge certificates remain in the final bounds.

Both chains still assume AllRefuted6K235 and AllRefuted236. Conditional 234
also assumes cases 7301, 7302, 7303, 7307, 7308 with refutation caps 15, 17, 15, 15, 15,
equivalently floors (16,18,16,16,16). Preserve the stopped original case7302
target 20 replay and its 649 successful modules. Any target 18 proof needs new
sources and evidence. Its old Check1 timeout was 900 seconds.

## Runtime, artifacts and publication

Use `milestones/100-prefix-potential-checker/scripts/check.py`, which snapshots
sources and checks dependencies, axioms and exact object/log bytes. Its
environment reuses milestone 99 and the milestone 98 support overlay. Do not
recopy the 3.3 GB overlay. Compile sequentially; keep at most three Lean jobs.
Do not add `-M4096`. Inspect live processes and records before any restart;
old active markers may be historical. Never edit a live checker or source.

Python is
`C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`;
use `-B -X utf8`. Numerical packages are in `work/solver_packages`.
Lean 4.19 and mathlib are under
`D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research`.

Keep exact milestone bytes and manifests. Preserve unrelated `.gitignore`
and `milestones/50-three-count-return/excess-screen/data/critical-family.json`
changes. Fetch before committing, stage only reviewed files, verify staged
bytes and push after each completed research round.

The paper remains revision 96, with unchanged authors and hyperlink settings.
The next full revision is 106. The open source is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`; the mirror is
`E:/Snake-in-a-box/paper/snake9_research.tex`. Revise the open source in place
when due, keep the mirror identical and compile through the built-in tool.
Use standard notation; introduce a definition only when necessary and reused.
