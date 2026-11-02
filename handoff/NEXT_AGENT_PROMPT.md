# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
102's mathematical note, proof summary and audit/next-optimization.md. The
previous round made progress: all 412 fixed potential-block equations and
eight new complete profile/context checks passed. The active goal is unresolved.

## Next task

Retain the original decidable leaf comparison. Reduce repeated potential-tree evaluation inside the prefix check, following the feasibility note. Prove the traversal invariant and needed tree-shape facts before running a bounded comparison. Use the checked block equations and bounded transfer, preserve the original min caps and every accepted code, and extend the remaining finite certificates once the method is verified.

The existing block equalities are Snake9.PotentialBlocks102.completed_at_i
and conditional_at_i for i from 0 through 205. Each takes offset and a proof
offset<7776, and returns the exact original capped potential value at its
recorded subtree. The source offset code/6 requires code<46656; the target
offset code%7776 is always bounded. No equality for arbitrary source codes
was introduced. Root selections are checked by Lean against the original table.

The generic transfer is
Snake9.BoundedPrefixTransfer102.contextCheck_of_bounded_prefix, with arguments
test, w, P, pi, direction, history, class, block equality, successful prefix
test, and pointwise test equality on accepted codes below 46656. It proves
the original contextCheck. It introduces no new actual-snake premise.

Reuse every complete context listed in milestone 102's proof summary:
the completed profile at 35/0 and conditional profile at 177/43 from milestone 100;
both profiles at 99/37 from milestone 101; and both profiles at 0/0, 1/0, 9/0
and 10/0 from milestone 102. There are six per profile.
The new versions of 99/37 are comparison checks and add no coverage.
The context-specific formulas in milestone 101 remain available for all 791
contexts; no replacement graph or weight model is required.

The observed fixed-block timings at 99/37 are 56.860 s and 110.016 s, compared
with archived times of 111.750 s and 194.312 s. Workloads differed; do not state
a controlled speedup factor. The proof summary also records a fresh sequential
pair for direct Boolean versus decidable comparison. Both variants are checked;
their timings are one-context observations. The full graph still has 785
unproved contexts per profile.
Avoid simply launching all remaining expensive checks before testing the next
credible reduction. Preserve all successful certificates.

The matched Boolean experiment observed 61.672 s for the decidable comparison
and 92.234 s for direct Boolean comparison. Retain the decidable comparison;
this one pair supplies no performance improvement to pursue. It does not
establish a universal ordering of the two variants.

The proposed next traversal is unimplemented and unverified. Its source
potential uses the first five of six symbols and its target the last five.
The feasibility note identifies the shape and offset obligations. Confirm
those obligations and a bounded benchmark before claiming it is useful.

No compiler is active at this checkpoint. The unavailable redundant Omega
import failure is preserved and superseded by the corrected successful source.

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

Use `milestones/102-potential-block-reduction/scripts/check.py`, which snapshots
sources and checks dependencies, axioms and exact object/log bytes. Its
environment reuses milestone 101 and the milestone 98 support overlay. Do not
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
