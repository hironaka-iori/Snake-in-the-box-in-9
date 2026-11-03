# Checked initial state and first replay block for 012032

The exact count-free 012032 core now connects, in Lean, to the materialized
initial proof state and to a verified checkpoint after the first 32 replay
segments. This closes the initial-state requirement left in milestone 150.
It does not yet establish the complete contradiction.

## What is checked

All 38 pilot modules passed, with 120 accepted axiom reports. They connect
all 13,655 retained clauses, partitioned into 107 chunks, to the initial
tree and check the first 2,169 deductions with 6,151 propagation references.
Every assignment satisfying the retained core therefore satisfies the
checkpoint obtained by this prefix.

Eleven further module checks extend the result through the first 32
segments: 3,728 deductions and 195,386 references. The final check in this
block verifies the next stored checkpoint, and the block theorem transfers
truth to it. The two prefix counts overlap; they must not be added.

There are 49 accepted modules out of 342 in the complete generated replay.
The complete source contains all 878 segments, 27 transitions between
stored checkpoints, and the final empty clause. The independent source
audit matches every packed deduction and all saved checkpoints, and verifies
that every group occurs in the final composition. Its source inspection
does not replace checking the remaining proof in Lean.

## Mathematical consequence and limitation

The completed result in milestone 150 says that unsatisfiability of this
exact core implies

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16
\]

for every fitting actual-snake window with canonical directions 012032,
including reversal. There is no additional pair-count, parity or specified
endpoint-position assumption. The present checkpoint checks part of the
contradiction needed by that implication. The remaining 846 segments and
final assembly must pass before the actual-snake share theorem is complete.

No new global upper bound follows. Even a completed local share theorem
would discharge only one premise of the conditional 234 profile. The other
local floors, remaining reference refutations and complete potential
certificate remain separate. The maintained interval 191--235 retains the
contributor independent-rebuild limitation. The value 196 and the optimum
remain unresolved.

## Selected continuation

Prioritize the remaining 012032 replay: the new certificate has 342 modules
and 5,350,080 references in total. The existing 012301 job is preserved and
has resumed. These are measured certificate sizes; no full-run timing
improvement is asserted.

Before a new full run, revalidate the existing process and the exact 151
plans and accepted receipts. Use a guarded controller to hold the existing
147 coordinator between checks, run the 151 full replay, and resume the same
147 process afterward or on controller failure. Do not start a second Lean
compiler directly. The first-group controller is limited to 11 new modules;
it is not the controller for the remaining full replay.

Reuse the 49 accepted objects only after matching source, object, log and
dependency hashes. On another machine, restore the archived sources and
rebuild the required dependencies; the current reuse driver assumes the
saved local objects and runtime paths exist. Do not change a receipt to
represent a rebuild that was not executed.

After all 342 modules pass, audit the final unsatisfiability statement and
compose it with the already checked actual-snake implication. Retain the
other upper-bound premises throughout.

## Files and reproduction

`data/pilot-completion.json` and `data/first-group-completion.json` contain
the accepted results. `data/full-execution-plan.json` gives the dependency
order. `data/first-group-progress-snapshot.json` is immutable; the live
`data/full-replay-progress.json` may change when the work resumes and is
excluded from the publication manifest.

All 342 generated sources are preserved in byte-verified archives and remain
available locally. Restore missing files with `scripts/restore_archives.py`.
The full-source plan retains an older command filename in its metadata;
the correct local generator is `scripts/emit_full.py --full --max-source-mib 256`.
The recorded generator hash and generated proof bytes are correct. The
exact packed input remains in milestone 150 and its verified archives.

The paper is updated in both existing locations without new definitions,
author changes or preamble changes. Source checks pass. The compiler helper
fails before TeX, so no new PDF is verified. Last full revision: 146; next: 156.
