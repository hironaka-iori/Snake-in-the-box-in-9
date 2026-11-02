# Milestone 102: bounded potential-block reduction

All 412 fixed-block equations passed Lean, together with the generic
bounded transfer to the original context checker. No definition was added.
The milestone contains 20 checked modules and 441
distinct theorem axiom audits. Successful sources contain no incomplete proof
or unchecked native evaluation; the permitted logical axioms are propext,
Classical.choice and Quot.sound.

Eight new complete profile/context checks passed:

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
| completed | 0/0 | 6,123 | 90.516 |
| conditional | 0/0 | 6,123 | 94.672 |
| completed | 1/0 | 6,997 | 85.984 |
| conditional | 1/0 | 6,997 | 119.219 |
| completed | 9/0 | 3,913 | 88.953 |
| conditional | 9/0 | 3,913 | 39.375 |
| completed | 10/0 | 4,474 | 45.250 |
| conditional | 10/0 | 4,474 | 43.531 |

Including the earlier certificates, coverage is:

| Profile | Complete contexts | Accepted edges | Remaining contexts |
| --- | ---: | ---: | ---: |
| completed | 6 | 34,701 | 785 |
| conditional | 6 | 34,148 | 785 |

Each context certificate covers all 46,656 candidate codes through the
checked acceptance test. Counts for different profiles are kept separate.
The repeated comparison context 99/37 adds no coverage.

For that same context, the recorded timings are:

| Profile | Archived implementation, seconds | Fixed-block implementation, seconds |
| --- | ---: | ---: |
| completed | 111.750 | 56.860 |
| conditional | 194.312 | 110.016 |

The archived and current runs had different workloads. These are observed
timings, without a controlled speedup claim or an extrapolation to all contexts.

A separate matched pair changed only the leaf comparison in completed 99/37.
The decidable comparison took 61.672 seconds and direct
Boolean comparison took 92.234 seconds. The runs were sequential,
with no other Lean process at launch. Both prove the same original context
statement. This is one pair; it does not establish performance on other contexts
or isolate unrelated system activity. The semantic equality is checked in Lean.
The direct Boolean variant was slower in this pair and is not adopted as an
optimization. This observation does not prove it is slower in every context.

Read the [mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), [checkpoint](data/checkpoint.json),
and [next optimization analysis](audit/next-optimization.md).

The [contributor handover review](audit/remote-review.json) records the separate
branch's pending 234 construction. Its remaining builds do not supply a
completed certificate for this model.

The candidate JSON records proposed data; current proof status comes from
the individual Lean receipts and the proof summary. The global interval
remains 191 through 235 edges; 234 is conditional.
