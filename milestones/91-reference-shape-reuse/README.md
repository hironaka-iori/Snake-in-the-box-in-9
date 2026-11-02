# Milestone 91: certified reference-pattern reuse

The reference-pattern cache is sound and its six-direction pilot passes Lean.
The experiment supplies **eight new theorem audits**. It establishes no
consistent performance advantage over the direct checker, so the full witness
batch will use the existing direct balanced-lookup method.

The [mathematical note](mathematical-note.md) defines a certified shape table
and proves the substitution argument. The [proof summary](data/proof-summary.json),
[benchmark summary](data/benchmark-summary.json) and
[independent review](audit/cache-pilot-review.md) state the exact checked scope.

## What is checked

Three generic audits prove that bounded lookup into a valid shape table,
together with equality to the complete requested descriptor, supplies the
original reference compatibility test. Catalogue, placement, direction and
history bounds remain unchanged. Other witness families retain their original
compatibility checks. Equal list lengths prevent the zipped check from
discarding entries.

Five concrete audits check the 156 cached patterns, the two count lists,
all six assignments and the resulting membership theorem. The six assignments
use the original 640 boxes and original witness lists. Their 3,732 reference
entries use 26 cached patterns per direction; 108 other entries use unchanged
compatibility checks. Every cache descriptor is used and checked.

The final theorem has the direct pilot's exact hypotheses and conclusion:
for a listed direction/list assignment, every history below 75 and code below
46,656 retained by the original predicate belongs to the original class-1
diagram. Neither pilot imports the other's membership theorem. The full
791-context assignment and all-context finite coverage remain open.

The direct source is byte-identical to milestone 90 and its two theorem audits
are repeated for comparison. Repeated trials do not add new results. Printed
axiom dependencies are subsets of `propext`, `Classical.choice` and `Quot.sound`;
these concrete checks are not axiom-free. No checked source uses `sorry`,
`admit` or `native_decide`. The inherited proof environment is reused.

## Completed comparison

Fresh compiler processes ran in the order direct, cached, cached, direct.

| Method | First proof run | Second proof run |
| --- | ---: | ---: |
| Direct | 18.812 s | 37.875 s |
| Cached | 24.203 s | 28.016 s |

The cached proof times include shape validity, both count lists, all index
lengths and descriptor correspondences, remaining guards and final assembly.
Its generic setup took 46.125 seconds and cache-data compilation 45.219 seconds,
separate from these proof runs. Generation and existing shared dependencies
are excluded. Two other Lean processes were active before each trial. Their
load was not controlled, and only two trials per method were taken.

The observed order changes between runs. No speed advantage is established.
The direct checker avoids additional cache setup and will be expanded to the
saved 507 base jobs and three history heads. Preserve the cache theorem; a
new benchmark would require a materially different representation or purpose.

All trial logs and receipts are immutable copies. The canonical audit for a
repeated module refers to its final trial. Source and object hashes agree
between repeats. The checker uses unique temporary output paths and saves
process inventories for the comparison.

## Continuing jobs and next work

The frozen checkpoint observes **geometric classes 0 through 19** completed
in the existing 127-class run, tool session **23168**. Seven classes completed
after milestone 90, adding 28 geometric theorem audits outside this milestone's
eight new audits. Newly completed immutable receipts and logs are saved here
through the manifest.

The existing case7302 replay, tool session **14427**, has **493 distinct
successful modules** at this snapshot, 44 more than milestone 90. Its final
local-share theorem and audit remain pending. Raw repeated composition rows
are counted separately. Both jobs continue; inspect actual process state
before any restart. Frozen observations may lag later progress.

The next work is to expand the direct witness checks from the milestone 90
pilot using the saved job plan. Preserve the three history witnesses at their
original leading positions. Combine the resulting validity with completed
geometric covers, then certify all context assignments, full-key membership
and endpoint identities. The two reference-catalogue premises, pending local
shares, credit interpretation and complete potential check remain explicit.

The replay entry points are:

```text
python scripts/check_shape_cache.py
python scripts/check_pilot.py
python scripts/verify_saved.py --verify
```

The pilot checker intentionally repeats proof compilations for the specified
comparison. The experiment is complete; it need not be rerun to continue
research. Use existing successful receipts when their dependencies match.
Build objects remain saved locally and excluded from Git. The
[checkpoint](data/checkpoint.json) and [manifest](data/file-manifest.json)
preserve exact evidence and current handover versions.

Bounds remain **191 through 235 edges**, with **234 conditional**. The 235
upper bound uses the inspected contributor theorem and saved audit; a full
independent rebuild remains pending. The paper is unchanged at revision 86,
with its three authors and hyperlink settings preserved. The next full
paper revision is scheduled for milestone 96.
