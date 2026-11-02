# Milestone 100: checked prefix traversal and complete contexts

Lean now certifies two complete defined-graph contexts, covering 13,749 accepted
edges. The implementation combines a proved prefix traversal with exact
context-specific weight and endpoint equalities. Five modules and 25 theorem
audits passed; the complete finite graph certificates remain pending.

## Verification

Five modules passed with 25 theorem audits. Both complete contexts transfer to
the original context checker, using the exact original weights, endpoint
functions and potential candidates. No extra hypothesis is needed for either
finite context theorem.

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
| Completed | 35/0 | 7,151 | 121.703 |
| Conditional | 177/43 | 6,598 | 165.719 |

Each proof covers every one of the 46,656 codes in its context, with rejected
branches omitted by the checked soundness argument. Together the two contexts
contain 13,749 accepted edges. The earlier 207 accepted pilot edges lie inside
these contexts and are not additional coverage.

The old pointwise completed-context attempt and the prefix traversal with
unreduced weights both reached their 300-second limits. Those attempts remain
preserved. The successful checks also use exact context simplifications, so
the measured improvement concerns the combined implementation. The numerical
transition counts alone do not predict the compiler runtime.


Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
and [prefix enumeration audit](data/prefix-enumeration-audit.json).
The maintained interval is $191\le a(9)\le235$ edges, with 234 conditional.
Original case7302 evidence and both manuscript copies are unchanged.
