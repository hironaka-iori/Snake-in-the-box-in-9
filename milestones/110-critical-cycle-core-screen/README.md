# Milestone 110: a checked critical-cycle count exclusion

The count pattern `(5,5,2,4,5)` cannot occur on a six-transition window with
canonical directions `012340`. Lean checks this for actual snakes and
checks both orientations used in the graph. No new mathematical
definition was introduced.

Read [the mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), and
[independent review](audit/final-review.md).

The new theorem removes 865 additional graph keys. Exact native
calculations preserve mean/range 483/551 for the completed profile and
496/602 for the conditional profile. Assuming all seven proposed count
exclusions removes 4,773 additional keys and still preserves those
comparisons. This round does not improve a numerical upper bound.

- `lean/PlainCount110.lean`: actual-snake theorem and graph applications.
- `lean/Recovered110/`: the 64 checked proof and semantic modules.
- `data/*-audit.json`, `logs/`: exact receipts, attempts, source snapshots.
- `work/renumbered/`: final CNF and LRAT, checked independently in `scripts/audit.py`.
- `data/plain-probes/`: seven initial native probes; only one now has a checked theorem.
- `data/count-profiles-one/`: graph calculation using the checked exclusion.
- `data/count-profiles-all/`: hypothetical graph calculation using all seven.
- `data/share-profiles/`: hypothetical share-floor calculation, with unchanged comparisons.
- `data/all-core-screen.json`: scan of 143 archived proof roots.
- `data/cycle-screen.json`: no archived relaxed candidate hits the original limiting cycles.
- `upstream/`: exact archived inputs and pinned generators.

The initial `lean/LocalWindow*` and `generated-remapped/` files are export
stages. Only `lean/Recovered110/` and `lean/PlainCount110.lean` have the
final audited receipts. The old native probe records remain unchanged
to preserve their status at the time of discovery.

The next priority is a restriction covering a family of surviving count
patterns. Evaluate both profiles before certifying individual cases.
Milestone 104's original complete potential batch continues independently.
The remaining reference union has 1,366 unresolved entries. The paper
remains revision 106; its next scheduled full revision is 116.
