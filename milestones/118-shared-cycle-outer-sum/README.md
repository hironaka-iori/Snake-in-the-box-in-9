# Milestone 118: local counterexamples and count-sum limits

The proposed outer-four lower bound 13 on 012301 fails in the radius-four
local model. Two verified forests have counts (4,2,10,2,3) and (4,2,10,4,2),
clipping exactly to the completed and conditional cycle tuples from 117.
They have seven and four components. These are local counterexamples;
no complete-snake counterexample or extension is established.

Fourteen bounded attempts cover twelve distinct cases: ten positive local
witnesses and four UNKNOWN results. The unrestricted total18 witness has
counts (3,2,5,4,4); the middle-at-least6 total19 witness is (4,3,6,2,4).
Thus unrestricted total at least19 and middle-at-least6 total at least20
also fail locally. Total at most17, and middle-at-least6 total at most18,
remain UNKNOWN after preserving and extending their saved cycle cuts.

Even granting the remaining candidate bounds 18 and 19, the old cycles survive.
Their maximum means under the shared coefficient budget are 977/2 and 504.
Both are too small to improve their corresponding integer comparisons,
even at zero potential range. These are ceilings from retained cycles,
not newly attained whole-graph minimum means. No new rule was accepted,
no full graph optimisation was run, and no numerical bound improved.

Lean checks the exact counts and disjoint induced path components of both
critical forests, plus five coefficient and comparison deductions. Nine
axiom reports pass. Radius-four identification and interior endpoint counts
are independently checked in Python. The first broader Lean attempt timed
out after 120.438 seconds; its exact source, checker and log are retained.
The split check passed in 30.735 seconds. No new mathematical terminology
or paper definition was introduced; four private constants store reused
concrete vertex data in the Lean source.

At the process-verified checkpoint, 104 reports 157/791 contexts in each
profile and 115 reports 193/1397 modules. Both drivers remain live; neither
was restarted or edited. Final potential assembly and the 115 actual-snake
theorem remain pending. The 117 local count contradiction still awaits
concrete Lean semantics and its full replay.

The maintained interval remains 191 through 235 edges, with contributor
proof and archived audit for 235 and its complete independent rebuild
pending. Conditional 234 and the exact optimum remain unresolved. The
reference union still has 1366 pending entries. Paper revision 116 and
both source copies are unchanged; the next full revision is 126.

## Next bounded task

Continue the same count-sum and empty-square route on 012304, the other
shape shared by both surviving cycles. Inspect existing witnesses first.
The completed profile has bucket tuples (2,6,2,4,6) and (2,6,2,3,6);
the conditional profile has (2,6,4,2,6) and (4,6,2,4,6). Every symbol 6
represents [6,21]. Test coupled sums or conditions that cover those full
intervals. Before investing in a large refutation, compute its best possible
credit on both saved cycles under the shared budget. The 118 analysis shows
that proving only the two remaining 012301 total candidates cannot improve
the integer bounds in this fixed family.

## Evidence and reproduction

- `lean/Witness118.lean` and `data/Witness118-audit.json`: checked concrete counts, path components and comparison deductions.
- `data/all-witness-audit.json`: all ten positive witnesses.
- `data/all-probe-audit.json`: all fourteen attempts, source pins and cycle cuts.
- `audit/witness-review.md` and `audit/final-review.md`: independent bounded reviews.
- `data/cycle-limits.json`: exact retained-cycle ceilings under the two stated hypothetical bounds.
- `data/batch-summary.json`: dated, process-verified observations of the existing proof batches.
- `data/file-manifest.json`: exact saved and published file scope.

Use the configured Python runtime to run `scripts/verify_saved.py --verify`.
The probe and audit scripts preserve existing result files and refuse to overwrite them.
The copied `evaluate_total.py` was not run in this milestone.
Native witness checks and Lean checks have separate scopes as stated above.
