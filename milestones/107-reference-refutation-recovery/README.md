# Milestone 107: first recovered reference refutation

The first entry of the exact reference union is now checked in the current
environment. It excludes directions 012 with internal singleton counts (1,1).
The resulting theorem has no local refutation hypothesis. Lean also proves
that the entire union obligation is equivalent to refuting its remaining
1,377 entries. No new mathematical definition was added.

Read the [mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json),
[recovery guidance](audit/recovery-guidance.md), and
[continuation record](../../handoff/NEXT_AGENT_PROMPT.md).

The recovered Q012A11 input and semantic source come from the exact pinned
contributor tree. The 1,172-clause core matches that source. CaDiCaL produces
a fresh LRAT proof, which is reduced to 968 lemmas and 41,184 hints and
checked both by a separate plain-clause interpreter and by Lean. The final
isolated replay has 19 checked modules and 14 theorem axiom reports.

The first replay checked the local modules but its combined wrapper failed
because Lean resolved a shared module directory through the new local prefix.
The successful replay uses the unique import prefix Recovered107. Only
import paths changed; mathematical namespaces, clauses, declarations and
proofs were preserved. Both attempts and all successful receipts remain saved.
Existing shared proof objects were reused; no full clean dependency rebuild
is asserted.

A source comparison identifies 143 exact alternative entries in the older
direction catalogues, including the recovered first key. The other 142 are
candidates for smaller proof inputs, with no new replay implied by this
comparison. Union entry 472 has an available 120-clause alternative and is
the next proposed test. The recovery guidance records the exact scope.

The maintained interval remains 191 through 235 edges. The contributor's
235 proof retains its archived audit and pending independent rebuild.
The target 234 and exact optimum remain unresolved. Milestone 104's complete
potential batch continues independently. The paper remains revision 106;
the next scheduled full revision is 116.
