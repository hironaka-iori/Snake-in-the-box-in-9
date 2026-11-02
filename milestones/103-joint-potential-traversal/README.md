# Milestone 103: joint potential traversal

Lean checked the general implication from successful joint traversal to
the existing prefix checker. Both source and target digit schedules, the
rejected-branch rule and the potential-width checks are covered. There are
11 checked modules and 26 distinct theorem axiom audits.
Only two reusable implementation definitions were added: branch selection
and joint traversal. No mathematical terminology or manuscript definition was added.

Four matched sequential comparisons passed, including transfer to the
original full context checker:

| Profile | Direction/history | Baseline seconds | Joint seconds |
| --- | --- | ---: | ---: |
| completed | 99/37 | 58.703 | 83.422 |
| completed | 0/0 | 59.734 | 85.609 |
| conditional | 99/37 | 61.734 | 29.969 |
| conditional | 0/0 | 122.250 | 71.766 |

Each pair uses the same imports, weights, potential roots, clipping bound,
acceptance root and candidate codes. No other Lean compiler was active at
launch. These are end-to-end module times from one pair per profile and
context; unrelated system activity was not isolated. They do not establish
a universal performance ordering.

The provisional batch choices, based on total time for the two contexts in
each profile, are completed: baseline; conditional: joint.
The batch should preserve a fallback for a context that exceeds its limit.

These contexts were already certified. Coverage therefore remains six of
791 contexts per profile: 34,701 accepted edges for the completed profile
and 34,148 for the conditional profile. There are 785 contexts per profile
still pending. Comparisons do not add distinct graph coverage.

Read the [mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), [checkpoint](data/checkpoint.json)
and [source review](audit/traversal-review.md). The candidate metadata records
generated proposals; proof status comes from the checked receipts.

No improved global snake bound is claimed. The next step is complete,
resumable graph certification with verified reuse of identical checks.
