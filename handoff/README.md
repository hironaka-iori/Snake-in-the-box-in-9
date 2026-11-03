# Research handover

Read [current status](CURRENT_STATUS.md), [next steps](NEXT_AGENT_PROMPT.md),
and [milestone 117](../milestones/117-cycle-sum-refinement/README.md).

The new candidate on 012034 states that a middle count at most 5 forces
the outer four counts to sum to at least 16. Both previous attaining cycles
violate it. A complete native contradiction passes independent replay.
The reduced proof has 142,180 deductions and 8,712,029 hints, using 1,709
variables. Its 5,114 used clauses map exactly into the original formula.
The earlier proof is preserved. Concrete sum semantics and the full Lean
contradiction remain pending.

Lean checks the actual-snake transfer with that local contradiction as an
explicit hypothesis, plus two comparison deductions. One module and three
standard axiom reports pass. No mathematical definition was added. The first
attempt launched no compiler because the memory gate was closed; the waited
retry passed. Both attempt records remain saved.

The new rule removes 23,285 further graph edges. The completed-floor mean
increases from 6309/13 to 2915/6, with range 1730/3 and comparison 1324108/5623.
The conditional-floor mean/range remains 496/602. Integer comparisons remain
235 and 234. Both experiments assume unproved local rules. Independent
saved-cycle and potential audits pass; the producer supplies the all-edge
lower certificates.

All applicable deficits vanish on the replacement 18-edge and 3-edge cycles.
Changing coefficients within this eleven-rule family cannot improve their
mean ceilings. Range reduction alone also cannot improve the integer bounds.
The next shared target is 012301, with exact outer sums 11 and 12 and middle
count in [6,21]. An outer lower bound 13 remains an untested candidate.

The independently checked local witness (5,3,5,3,6) has outer sum 17 and five
components. It is not a complete snake. Outer sum at most 16, unrestricted
total at most 20, and total at most 20 with all counts at most 5 remain UNKNOWN
in bounded runs. The candidate lower bound 16 is not shown sharp.

At this process-verified snapshot, milestone 104 reports
152/791 completed-profile and 153/791 conditional-profile contexts;
milestone 115 reports 159/1397 checked modules. Both drivers are live.
Their final certificates and the 012310 actual theorem remain pending.
Neither batch was restarted or changed.

The maintained interval remains 191 through 235 edges, with the contributor
proof and archived audit for 235 and its complete independent rebuild pending.
Conditional 234, the optimum and 196 remain unresolved. There are 1,366
outstanding reference entries. Paper revision 116 is unchanged; next revision 126.
