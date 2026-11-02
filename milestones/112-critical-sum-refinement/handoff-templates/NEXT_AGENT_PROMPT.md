# Continuation assignment

Continue the empty-square/count-sum route in `E:/Snake-in-a-box`. Read
milestone 112's mathematical note, proof summary, checkpoint and final
review. Verify milestone 104's current process before interpreting its
saved state. Keep the goal active and preserve that batch.

## Latest checked theorem

`ActualSum112.actual_outer_sum` proves, for a fitting canonical six-step
window `012314`, that middle count at most 2 implies outer sum at least
19. This is an actual-snake theorem without the collective catalogue
premise. Graph-orientation guards and the complete revised graph-to-snake
integration remain separate. The original reference union still has
1,366 unresolved entries; this theorem closes none of its original entries.

The native formula has 55,177 clauses and 2,793 variables. The original
certificate uses 3,577 input clauses, 5,061 deductions and 610,721 hints.
Native core refinement selects a 3,306-clause proof with 7,020 deductions
and 367,588 hints. A full variable bijection maps its 1,718 used variables
into `1..1718`, enabling the existing literal-offset checker. Independent
reconstruction and RUP replay verify both representations.

The final plan is `data/sum-plan.json`; the final generated sources are
under `generated-sum-remapped/` and isolated checked modules under
`lean/Refined112/`. The earlier `generated-sum/` output is an uncompiled
failed export. Preserve it and its recorded failure. Do not rerun
`prepare_sum.py` against existing native outputs. The later
`export_sum.py` reuses those immutable native reductions.

There are 36 generated proof modules plus `ActualSum112` and three checked
helpers, giving 40 successful records and 20 printed axiom reports.
The helpers are `SumCountSemantics112`, `SumGeometry112` and `SumBudget112`.
All source, object, log and receipt hashes are audited by `scripts/audit.py`.
A complete rebuild of historical dependencies remains separate.

## Generic interfaces now available

`SumCountSemantics112.countP_permuted_corners` proves that a sorted list
of negative primary literals represents a sum of absent-corner counts,
given its mapped-vertex permutation. Repeated occurrences must remain.
The new `012314` sum has 84 occurrences and 70 distinct literals; the
older milestone 111 `012340` sum has 84 occurrences and 77 distinct literals.
Do not mix these multiplicities. `sound_append_sum` supports one extra
sum counter after the ordinary validated counters.

`SumBudget112` combines an outer-four deficit with a total-five deficit.
Use fixed nonnegative integer coefficients `a,b` with `4*a+b<=120`.
The outer deficit receives coefficient `a`; the five-count deficit receives
`min(a,b)`. Take the maximum applicable credit. The shared shifted sum
is bounded by 120 times total excess above clipped count 6. The clipped
boundary contributes 21, hence 2,520 after scaling. Existing share credit
remains separate. Local sum lower bounds are explicit hypotheses.

## Conditional graph results and next test

`data/expanded-rules.json` contains seven rules. Only the new `012314`
rule is proved in this round; the other sum rules remain hypotheses.
The final `data/expanded24/results.json` removes 33,362 additional keys
beyond the checked three-count graph, leaving 4,909,227. Both edge-wise
integer potentials and attaining cycles are saved.

Balanced coefficients `(24,24)` give completed mean/range `484/557` and
comparison `1103389/4684`, whose floor is 235. The conditional mean/range
remains `496/602`, with comparison `551765/2348` and floor 234.

The completed six-cycle has all count symbols 4 and weights
`480,480,492,480,480,492`. The final conditional four-cycle has weights
`498,612,498,376`. All applicable deficits vanish on both cycles. They
therefore bound the means by 484 and 496 for every nonnegative coefficient
choice within this fixed rule family. Balanced coefficients attain both.
Do not repeat coefficient sweeps. The saved coefficient-screen JSON is
an earlier integer-only screen for the initial six-rule family; the final
zero-deficit cycle argument is stronger and applies to the expanded family.

Lean also checks the scaled arithmetic: when `p<=484*d`, the standard
comparison still permits length 235 for any nonnegative potential range;
when `p<=496*d`, it still permits 234. Improving potential ranges alone
cannot change these integer comparisons.

The next bounded research test is the all-4 tuple on direction shape
`012034`, followed by a broader count-sum restriction if it is impossible.
The proposed outer lower bound 17 under middle count at most 4 would
affect this obstruction, but its native cap-16 probe is UNKNOWN after
15 seconds. The unrestricted total-at-most-20 probe on the same shape
is also UNKNOWN. Do not turn either timeout into impossibility. Test any
stronger candidate on both full profiles before expensive proof export.

Six local witnesses independently falsify other attempted strengthenings
within the radius-four model. Their counts and components are recorded
in `data/witness-audit.json`. They have relaxed boundaries and multiple
components and do not construct complete long snakes. The 30-second
`012340-middle5-outer17` native proof-generation timeout remains preserved;
its partial LRAT is not checked and should not be restarted automatically.

## Preservation and outstanding work

The remaining reference union has 1,366 entries. The twelve checked
indices are `0,472,495,535,572,602,619,620,1006,1010,1011,1014`.
Conditional 234 still needs the remaining union, complete potential
assembly, five local floors `(16,18,16,16,16)`, and compatible concrete
integration. Preserve the stopped old 7302 target-20 batch.

Milestone 104 continues checking the original graph potentials. Do not
change its active generator, checker or sources, or restart based on a
stale observation. Audit final coverage and axioms after it finishes.
Allow at most one additional Lean compiler under the saved memory gate.
Do not use `-M4096` or copy the 3.3 GB shared support overlay.

The maintained range is 191 through 235 edges, based on the contributor
proof and archived audit with a full independent rebuild pending.
Conditional 234 and any exact optimum, including 196, remain unresolved.

The open paper is `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`;
its repository mirror is `paper/snake9_research.tex`. Revision 106 is
unchanged; the next full revision is 116. Preserve Iori Hironaka, Tommy Ma
and Steven Zhan as authors and preserve hypersetup. The previous built-in
compiler failed before TeX execution, so no new PDF is verified. Use
ordinary notation and only essential, repeatedly used definitions. Keep
implementation filenames out of the mathematical manuscript.

Python is `C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`
with `-B -X utf8`. Lean 4.19 and mathlib are under
`D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research`.
Push each completed round after checking incoming GitHub changes.
Leave unrelated `.gitignore` and milestone 50 critical-family edits untouched.
