# Milestone 108: one smaller proof covers seven reference entries

Lean checks a stronger version of the recovered direction-window exclusion.
For the direction word 012304, the five internal singleton-square counts cannot
simultaneously satisfy the upper bounds 2 at the first centre, 2 at the fourth,
and 3 at the fifth. The second and third counts may range from 0 through 21.
The statement uses the existing local snake axioms. No new mathematical
definition was introduced.

The 120-clause archived core has a regenerated contradiction with 75 steps and
426 antecedent references. Its clauses match the archived full formula exactly.
The ordinary and relaxed semantic arguments both pass Lean. A separate
plain-clause check verifies the contradiction independently of its exporter.

Bounds weakening transfers the relaxed result to seven exact reference keys.
Together with milestone 107's first entry, eight entries are now discharged.
Lean proves that the original 1,378-entry obligation is equivalent to the
filtered list of 1,370 remaining entries. Nine final modules and fifteen
printed theorem axiom reports pass. Existing shared dependencies were reused.

Read [the mathematical note](mathematical-note.md),
[the proof summary](data/proof-summary.json),
[the checkpoint](data/checkpoint.json), and
[the continuation instructions](../../handoff/NEXT_AGENT_PROMPT.md).
Source reviews and preserved failures are in [audit](audit/attempts.md).

The maintained interval remains 191 through 235 edges. This round supplies
checked restrictions shared by the two bound arguments; it does not improve
their numerical conclusions. The complete graph batch remains separate.
The manuscript remains revision 106; its next full revision is scheduled
for 116. The exact optimum and conjecture 196 remain unresolved.
