# Milestone 112: an actual count-sum theorem and shared charging

For canonical directions `012314`, a middle count at most 2 forces the
four outer counts to sum to at least 19. The complete contradiction,
counter semantics and transfer to actual snakes pass Lean. The final
theorem has no collective catalogue premise. No new mathematical
definition was introduced.

Read [the mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), and
[independent review](audit/final-review.md).

The seven-rule conditional graph experiment improves the completed mean
to 484, with potential range 557. The conditional mean/range remains
496/602. Integer comparisons remain 235 and conditional 234. Surviving
cycles receive zero deficit credit under every coefficient allocation,
so changing coefficients alone cannot improve this fixed family.

- `lean/ActualSum112.lean`: the actual-snake theorem and comparison barriers.
- `lean/Refined112/`: final checked concrete semantics and contradiction.
- `lean/SumBudget112.lean`: shared four/five-position budget and clipped boundary.
- `lean/SumCountSemantics112.lean`: multiplicity-preserving sum-counter interface.
- `lean/SumGeometry112.lean`: geometric transfer with an explicit local contradiction.
- `data/sum-plan.json`, `data/*-audit.json`, `logs/`: 40 successful module records and 20 printed axiom reports.
- `data/expanded24/`: final native graph experiment, matching cycles and potentials.
- `data/probes/`, `data/witness-audit.json`: six independent local-witness checks and all bounded probe outcomes.
- `data/sum-renumbering.json`: exact variable bijection used by the final proof.
- `data/large-artifact-archives.json`: verified transport archives; raw originals remain locally.

`generated-sum/` is the initial uncompiled export. Its literal offset was
too small for the original variable labels. `generated-sum-remapped/`
and the isolated sources in `lean/Refined112/` are the final export.
The separate `012340-middle5-outer17` proof-generation attempt timed out;
its partial LRAT is not a verified certificate.

Other sum hypotheses, graph-orientation guards, complete revised-graph
certificates and concrete global integration remain pending. The maintained
range is 191 through 235 edges, with the full independent rebuild of the
archived upper-bound proof pending. Neither conditional 234 nor an exact
optimum is established here. Milestone 104 continues. Paper revision 106
is unchanged; the next full revision is 116.
