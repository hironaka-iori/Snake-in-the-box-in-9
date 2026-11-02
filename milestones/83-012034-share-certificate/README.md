# Milestone 83: the 012034 share target

This round pursues case 7302: every six-transition window with direction pattern
012034 should have a five-centre scale-12 share sum at least 20. The matching
native refutation is verified, and its Lean interpretation and replay are in
progress. The local theorem remains pending until the final case audit passes.

A separate 60-second test of the stronger floor 32 returned UNKNOWN, with no
candidate forest. It supplies neither a counterexample nor a proof. Its exact
scope and source are saved in [stronger-probe/](stronger-probe/README.md).

The project interval remains **191 <= a(9) <= 235 edges**. The upper bound uses
the inspected contributor theorem and saved audit; its full dependency closure
has not been independently rebuilt here. The exact optimum and the conjecture
196 remain unresolved. The proposed 234 certificate retains its explicit
local and global obligations.

## Mathematical target

For five distinct coordinates a,b,c,d,e, all below nine, consider six successive
directions (a,b,c,a,d,e). If the window starts at r and fits in the snake, the
target is

\[
20\le\sum_{i=1}^{5}\sigma_{12}(p_{r+i}).
\]

Here the scale-12 empty-square share is the existing project definition. The
five singleton counts have only their universal bounds [0,21]; no additional
low-count or endpoint hypothesis is imposed. The reversed direction window
is included in the generated statement. Neither generated statement is treated
as checked before its replay and geometry receipts exist.

The chosen native instance uses cap 19 and no cycle cuts. Its 99,818 clauses
have a verified 15,446-clause core. Compact renaming uses 6,238 active variables;
the semantic interpretation includes 6,831 variables and 121 clause shards.
Independent review checked native/core/compact/Lean literal correspondence,
the induced seven-vertex window, and both geometric wrappers. See
[preparation review](audit/preparation-review.md).

## Exact conditional comparison

Adding only the unproved 012034 floor 20 to the completed-share graph raises
1,043,097 of its edge weights. An integer potential and an attaining cycle
give the exact finite mean

\[
\mu=\frac{9259}{19},\qquad R=\frac{11301}{19}.
\]

The recorded potential is scaled by 19, so its stored range is 11301.
All 4,947,008 edge inequalities were checked again by a separate verifier,
which also checks the cycle, source arrays, weight hashes and precise single
additional premise. The current budget would then give

\[
89059m\le20965613,
\qquad m\le235.
\]

Three Lean audits check this conditional arithmetic and the fact that even
zero potential range cannot make this mean reach the 234 criterion. At this
scale the deficit is

\[
111960\cdot19-227\cdot9259=25447>0.
\]

Thus proving case 7302 strengthens the comparison but does not suffice by
itself to improve its integer bound. The finite model still requires an
actual-snake interpretation and complete Lean potential replay. The local
7302 premise itself remains pending in this checkpoint.

## Proof work and continuation

The case sources, compact proof and live compiler records are in
`../73-countfree-share-catalogue/cases/case7302/`. The selected native evidence
is `pysat2-cap19-certificate.json` in milestone 72's `critical-current/data/`.
The compact proof generation returned exit code 20. The original export and
the reduced export both passed independent simulation. The selected proof has
389,216 derived clauses and 25,783,817 hints, reduced from 548,140 clauses and
33,454,760 hints. It uses 27,815 slots, 15-bit encoding, 858 segments and
143 checking modules. All input clauses are unchanged. Lean replay is active;
the final local theorem remains pending.

The case-specific slicing script adapts the already used case7305 algorithm
only for the case number and task directory. It preserves all input clauses,
keeps the original proof and receipts, and requires independent simulation
before selection. Inspect current processes and saved receipts before
resuming; never duplicate a live semantic or replay driver.

Read the current checkpoint for the latest completed modules and live process
observation. A historical successful-row snapshot is not evidence that a
process is still running. The final success gate remains the case's
`data/proof-audit.json` with status `PASS_LOCAL_SHARE_THEOREM`, including
geometry and reversal. Until then, keep all five target local cases pending
in the combined catalogue.

## Reproduction and saved evidence

All 1,135 selected Lean sources are archived. The original CNF and LRAT,
generation/export metadata, and unsliced-source hash manifest are also archived.
The superseded 1,303-file unsliced Lean export remains local under the case's
`build/lrat-slice-21fb3e526fcb/original-lean/` and is excluded from Git archives.
Exact regeneration of that superseded tree was not rerun in this round and is
unnecessary for resuming the selected replay.

- `scripts/compare_target.py --assume=012034:20` writes this milestone's
  conditional model and potential without changing the completed comparison.
- `scripts/verify_comparison.py` verifies it without rerunning policy iteration.
- `scripts/check_arithmetic.py` checks the three Lean arithmetic statements.
- `scripts/slice_lrat.py 7302 --prepare` and `--select` are sequential, guarded
  proof transformations; inspect their prerequisites before running them.
- `scripts/restore_pending.py` restores the archived sources and proof bytes
  after a fresh checkout, verifying every member and rejecting different
  existing files. The oversized source archive is transported as three ordered
  parts; the helper first reconstructs and checks its exact original bytes.
  Compiled caches are excluded from Git, so a new host must rebuild the
  semantic modules and dependencies before resuming the final replay.
- [comparison-audit.json](data/comparison-audit.json) distinguishes the exact
  finite result from the unproved local premise.

The paper remains revision 76, with its existing editor and repository sources
unchanged. The next scheduled full revision is 86. Preserve all three authors
and the existing hyperlink settings.
