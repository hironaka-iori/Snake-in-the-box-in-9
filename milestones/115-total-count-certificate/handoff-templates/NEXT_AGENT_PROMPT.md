# Continuation assignment

Continue the count and empty-square route in `E:/Snake-in-a-box`.
Read milestone 115's mathematical note, checkpoint, proof summary and
reviews before choosing further work. Keep the overall research goal
active. The previous turn made concrete progress.

## Preserve and complete the live proofs

Verify both live processes from milestone 104 and milestone 115 before
changing their state. Milestone 115's batch driver is
`scripts/run_batch.py`; it checks the complete export and then
`ActualTotal115`. Its first six modules, including concrete semantics
and the first contradiction group, passed before the batch started.
The latest checked prefix is in `data/batch-progress.json`.

The selected `012310` proof has 287,753 deductions and 16,816,989 hints.
Independent RUP replay against original input IDs passed. The full
export's native simulation passed with 21,456 clause slots and the pinned
`LratFast15` checker. There are 2,139 active variables. The sum preserves
105 occurrences across 84 distinct vertices. One of the eight original
added cycle clauses is present in the selected core.

Do not count `ActualTotal115.actual_total_sum` as checked until its
receipt exists and its dependency closure passes. Its source is already
written. The batch has 1,397 modules, including the final composition.
Inspect failure logs and preserve failed attempts before any retry.
Keep the existing memory gate and avoid duplicate compilers.

## New distinct-direction candidate

For canonical `012345`, the proposed universal five-count lower bound
is 23. The negative probe is
`data/probes/012345-total22-long.json`: UNSAT in 28.391 seconds after
five validated cycle exclusions. The earlier 20-second attempt was
UNKNOWN and remains preserved. This formula has 3,589 variables and
59,448 base clauses, with five added cuts. Its sum contains 105 literal
occurrences and 89 distinct vertices. A concrete negative certificate
and Lean replay are still required.

`data/probes/012345-total23.json` supplies a directly checked positive
local forest with counts `(6,3,6,2,6)` and component sizes
`43,27,24,9,1,1`. The witness establishes local feasibility only.
All five saved positive models pass `data/witness-audit.json`.
`data/probe-audit.json` validates every added cycle cut and provenance,
without certifying the negative solver answers.

This universal statement supersedes the earlier middle-at-most-3
condition used to discover it. End caps alone, and end caps together
with middle at most 4, admit saved local witnesses. Avoid restoring
unnecessary hypotheses or proposing those weaker conditions as
contradictions.

## Numerical limits and next mathematical search

The final two saved graph experiments have means `6309/13` and `496`,
with valid ranges `7656/13` and `602`. The comparisons are
`4781536/20303` and `551765/2348`, retaining integers 235 and 234.
The new rules and several earlier rules remain assumptions.

The attaining cycles in the universal-total22 experiment contain zero
`012345` windows across all 64 placements. Increasing its lower bound
to 23 only deletes other edges or increases their weights, so the
previous potentials remain valid and those cycles retain their weights.
No further full scan is needed to establish unchanged means and preserve
the old valid ranges. This does not count new deletions or minimize the
range. Even a zero range cannot improve either integer at these means.

Choose future local restrictions by inspecting these actual replacement
cycles. Do not keep strengthening a direction pattern absent from them.
Keep conditional improvements separate from proofs using only completed
local results and a complete actual-snake interpretation.

## Paper and preservation

Full paper revision 116 is due next. Read and revise the existing open
source in place, preserve Iori Hironaka, Tommy Ma and Steven Zhan and all
hyperlink settings, then use the built-in compilation tool. Keep the
repository mirror synchronized. The paper should present mathematical
arguments without Lean filenames or implementation definitions.

Use the existing notation and ordinary prose. Add a mathematical
definition only when essential and used repeatedly. Preserve unrelated
`.gitignore` edits. Check GitHub and push completed research checkpoints.
Use `verify_saved.py --restore-archives` before compilation on a fresh
checkout and `--verify` to check the frozen package.
