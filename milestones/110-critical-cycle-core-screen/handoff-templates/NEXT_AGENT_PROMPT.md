# Continuation assignment

Continue the empty-square route in `E:/Snake-in-a-box`. Read milestone
110's mathematical note, proof summary, checkpoint and final review.
Verify milestone 104's saved progress against its actual process. Keep
the full research goal active and leave the running batch intact.

## Latest checked result

`PlainCount110.lean` proves that counts `[5,5,2,4,5]` cannot occur on an
actual six-transition window with canonical directions `[0,1,2,3,4,0]`.
It also proves the two graph-orientation guards at count offsets 0 and 1.
The final theorem has no collective reference-catalogue premise.

The local formula has 59,251 clauses and 3,484 variables. The checked core
has 1,664 clauses; a regenerated contradiction uses 2,007 deductions and
177,364 hints. The final proof renumbers 1,069 active variables first and
updates all meanings/counter literals. Sixty-four modules under
`lean/Recovered110/` plus `PlainCount110` pass. Six axiom reports are audited.
`scripts/audit.py` independently replays the exact renumbered proof and
checks source/object/log/receipt hashes. Imported dependency objects are
reused from the previously audited environment; a clean complete rebuild
remains separate.

The original export files under `lean/LocalWindow*` are preserved but
are not the final checked modules. `generated-remapped/` holds the
pre-isolation export. `data/isolated-plan.json` pins the import-only
transformation. Use unique import prefixes for new work; avoid shadowing
old `LocalWindowCnf`, `LocalWindowSat` or `LocalWindowUnsat` directories.

## Numerical result and next test

The new theorem excludes 865 extra accepted keys beyond the 2,092 from
milestone 109, leaving 4,944,051. The previous displayed mean-483 cycle
is broken, but another cycle preserves mean 483/range 551. Conditional
mean 496/range 602 also survives.

All seven targeted count probes returned native UNSAT. Six used no extra
cycle cuts; edge 2139224 used three. Only edge 3534483 has a checked theorem.
Even assuming all seven exclusions removes just 4,773 additional keys
and preserves both numerical comparisons. Hypothetical share floors 76
on the same seven patterns also preserve them. The full 143-root archived
core scan found no relaxed box that hits either original limiting cycle.
Do not repeat these screens without changed assumptions.

Next seek a single count inequality or interval restriction that excludes
a family of surviving configurations. Examine the exact cycles saved in
`data/count-profiles-all/results.json` first. The completed-profile cycle
has cyclic count pattern `[2,5,6,3]`; the conditional cycle has `[4,3,5,4]`.
Symbol 6 means actual count between 6 and 21. The data include complete
directions, history, state endpoints and count codes; these are finite-model
cycles, with no actual-snake realization asserted.

Test a candidate family restriction on both full graph profiles before
investing in large proof generation. Broadening the proved case by using
which counter limits its contradiction actually needs is one possible
test, but no relaxed version has been established. Preserve the count
semantics, endpoint constraints and coordinate alignment in every attempt.
The six other isolated certificates are lower priority because their
combined numerical effect is already known.

All graph results in this milestone are native integer computations, with
matching minimum cycles and an inequality checked on every edge. They
are not complete Lean graph certificates or new global snake bounds.
Within the all-seven result, each rule's `additional_to_prior` field is
its marginal addition after both milestone109 and earlier listed rules;
use the aggregate 4,773 for the combined effect. The one-case result gives
the independent 865 count for the checked theorem.

## Preservation and outstanding proof obligations

The reference union still has 1,366 unresolved entries. The twelve proved
indices are 0,472,495,535,572,602,619,620,1006,1010,1011,1014. Use the latest
equivalence in `ReferenceCoverage109`; this new theorem is outside that
original union and does not reduce its residual count.

Milestone 104 continues checking complete original-graph potentials.
Do not modify its active generator/checker/source files, restart it from
a timeout or stale observation, or infer completion from its live status.
Audit final group coverage, dependencies and axioms when it finishes.
At most one extra Lean compiler is allowed, subject to the saved memory
gate. Do not use `-M4096` or copy the 3.3 GB shared support overlay.

Conditional 234 still requires the remaining reference union, complete
potential assembly, and the five local floors `(16,18,16,16,16)`. The old
7302 target20 proof remains stopped after its preserved timeout; a
target18 proof requires new files. Do not restart the old batch.

The maintained interval is 191 through 235 edges, based on the contributor
proof and archived audit with a full independent rebuild pending. Neither
196 nor another exact optimum is proved.

The open paper is `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`;
the repository mirror is `paper/snake9_research.tex`. Revision106 is
unchanged and the next scheduled full revision is116. Preserve Iori
Hironaka, Tommy Ma and Steven Zhan as authors and preserve hypersetup.
The built-in compiler previously failed before TeX execution; no new PDF
is verified. Introduce a definition only if essential and repeatedly used.
Keep implementation filenames out of the mathematical manuscript.

Python is `C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`
with `-B -X utf8`. Lean4.19 and mathlib are under
`D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research`.
Use explicit working directories, exact saved hashes and bounded attempts.
Push each completed round after checking incoming GitHub changes; leave
unrelated edits to `.gitignore` and the milestone50 critical-family file.
