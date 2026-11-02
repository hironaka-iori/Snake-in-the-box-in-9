# Milestone 109: a new actual-snake restriction and its graph effect

For any five consecutive distinct transition directions in a nine-dimensional
snake, Lean checks that the first, second and fourth internal singleton-square
counts satisfy at least one of: first count at least 2, second count at least 6,
or fourth count at least 3. The third count is unrestricted.

The proof relaxes an archived 441-clause certificate. Its regenerated
contradiction has 270 deductions and 1,343 antecedent references. The relaxed
semantics, actual-snake transport, both graph orientations, four further
catalogue entries and the exact remaining-list equivalence all pass Lean.
There are now twelve checked reference entries and 1,366 outstanding entries.
Ten final modules and sixteen printed axiom reports pass, including the
arithmetic showing that reducing the potential range alone cannot improve
either integer comparison while its sharp-cycle mean survives.

Exact enumeration shows that this restriction excludes 2,092 of the existing
4,947,008 accepted full graph keys. A separate experiment retains 4,944,916
keys. Both sharp cycles survive: the completed profile remains at mean 483
with potential range 551, and the conditional profile at mean 496 with range
602. The five current floor obstructions also survive. No numerical upper
bound improves in this round. The active original graph batch is unchanged.

The previous 012304 restriction removes no extra accepted key. A source screen
of sixteen small certificates suggests other relaxed boxes, but every screened
box misses both current sharp cycles. Rank future candidates by those cycle
hits before further proof replay or graph optimization.

Read [the mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json),
[restricted-profile calculation](data/restricted-profiles.json), and
[continuation instructions](../../handoff/NEXT_AGENT_PROMPT.md).
The source reviews, failed setup note and verification limits are in
[audit](audit/attempts.md).

The maintained interval remains 191 through 235 edges; 234 remains conditional.
The full reference union and complete graph proof still have outstanding
requirements. The paper remains revision 106, with the next full revision
scheduled for 116. No mathematical definition was added.
