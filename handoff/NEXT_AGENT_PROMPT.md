# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
101's mathematical note, checkpoint and proof summary. All 505 direction
equations and all 791 context equations passed Lean. The active goal remains
unresolved. Preserve standard notation and define only necessary, reused terms.

## Next task

Use the checked equations for all 791 contexts to extend the finite potential certificates. First test exact reduction of each fixed source/target potential lookup to its recorded subtree, retaining the original cap and proving the needed count-code bounds. Benchmark one context per profile before expanding. Reuse the four complete context certificates and preserve the reference/local premises.

The checked context families in namespace Snake9.Context101 are
selected_d_q, source_d_q, target_d_q, block_d_q, completed_d_q and conditional_d_q.
Direction lookups and conditioned-credit equations cover all 505 directions.
AllContextSpecializations101 imports every context without declaration
conflicts. The single emittedCredit helper keeps all original cap tests.

The explicit potential uses a balanced lookup over 206 blocks, each of size
7776. A fixed-block equality can reduce this repeated lookup to its recorded
subtree, while preserving the min551/min602 cap. Establish code/6<7776 from
code<46656 for the source; the target offset code%7776 is always bounded.
No performance gain from this proposed reduction is yet measured.
The source-block equation is not valid for arbitrary natural codes. Transfer
the bounded equality code by code with accepted_code_of_prefix_check and the
interval checker, or prove a bounded prefix congruence; do not use an
unrestricted rewrite under the count-code function.
PotentialChecker99.checkInterval_iff already introduces exactly the bounded
code obligation. Split on diagramKeep; a rejected code is immediate, and
accepted_code_of_prefix_check supplies the reduced inequality for an accepted
code. Rewrite the bounded potential equations at that point. This avoids
introducing a replacement context checker.

Reuse the complete finite theorems:

- Snake9.PrefixCertificates100.completed_context_reduced: completed35/0.
- Snake9.PrefixCertificates100.conditional_context_reduced: conditional177/43.
- Snake9.PrefixCertificates101.completed_context_99_37: completed99/37.
- Snake9.PrefixCertificates101.conditional_context_99_37: conditional99/37.

The first pair covers 7151 and 6598 accepted edges. The second pair each covers
6043 accepted edges. The latter share the same keys, so keep profile coverage
separate: 13194 completed and 12641 conditional accepted edges. Both profiles
still have 789 unproved complete contexts. Each context theorem covers all
46656 candidate codes with acceptance filtering.

EmittingReduction101 proves both weights agree at99/37. Rule000 contributes
19 if count symbols1 and2 (indexed from0) are at most2, and18 otherwise; the geometric and
floor credits do not change this history minimum. Four accepted codes activate
the stronger credit in both profiles. Their potentials and slopes differ,
so equal weights alone do not identify their finite inequalities.

The independent read-only review checked context data and import coverage.
The initial unqualified-canon pilot failure is preserved and superseded by
the corrected successful source. Do not repeat the old 300-second unreduced
context attempts. If needed, split a new check at the first count symbol and
assemble the six checked branches with PrefixChecker100 soundness.

The numerical582 joint context groups require exact Lean equality and
transport before reuse. Matching class roots or endpoint pairs alone is
insufficient. No compiler is active at the saved checkpoint.

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

Use `milestones/101-context-specialization/scripts/check.py`, which snapshots
sources and checks dependencies, axioms and exact object/log bytes. Its
environment reuses milestone 100 and the milestone 98 support overlay. Do not
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
