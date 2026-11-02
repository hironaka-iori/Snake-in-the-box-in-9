# Milestone 101: exact equations for every context

All 505 direction lookups and all 791 context equations passed Lean. The
context equations preserve the exact selected rule list, source and target,
acceptance class, and both weight profiles. They hold for every natural count
code. The combined import check found no declaration conflict.

The milestone has 30 checked modules and 5,767
distinct theorem axiom audits. The only permitted logical axioms are
`propext`, `Classical.choice` and `Quot.sound`; no incomplete proof or unchecked
native evaluation is used. Exact sources, snapshots, logs and dependencies
are recorded in the proof summary and individual receipts.

The complete finite checks now comprise two contexts per profile:

| Profile | Direction/history | Accepted edges | Compiler seconds | Milestone |
| --- | --- | ---: | ---: | ---: |
| completed | 35/0 | 7,151 | 121.703 | 100 |
| conditional | 177/43 | 6,598 | 165.719 | 100 |
| completed | 99/37 | 6,043 | 111.750 | 101 |
| conditional | 99/37 | 6,043 | 194.312 | 101 |

Direction 99/history 37 is checked under both profiles, so its 6,043 accepted
keys must not be counted twice as distinct graph edges. Coverage is 13,194
accepted edges for the completed profile and 12,641 for the conditional
profile. Each context theorem covers all 46,656 candidate codes through the
checked acceptance traversal. The earlier 207 pilot edges are already included.

The complete graph inequalities still need 789 contexts per profile. The
all-context evaluator equations do not discharge those finite inequalities.
Compiler times are observations from the recorded runs. Some equation batches
overlapped the independent finite-check queue, and memory limits temporarily
delayed new batches. These times are not a controlled performance comparison.

Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
and [independent source review](audit/independent-review.md).

The generated JSON files describe candidates at generation time. Current
proof status is supplied by the individual Lean receipts and proof summary.
The saved unsuccessful pilot attempt was caused by an unqualified identifier;
its source snapshot and log are retained. The corrected source passed.

The maintained interval is 191 through 235 edges; 234 remains conditional.
The complete graph certificate is pending for both profiles.
