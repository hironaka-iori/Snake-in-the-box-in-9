# Milestone 111: a three-count restriction and sum experiments

For canonical transition pattern 012340, an actual snake must satisfy
alpha at centre 2 at least 4, centre 3 at least 3, or centre 4 at least 6.
The outer two counts are unrestricted. The local contradiction and
both graph orientations pass Lean. No mathematical definition was added.

Read [the mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), and
[independent review](audit/final-review.md).

The new restriction removes 1,462 additional graph keys, leaving 4,942,589.
The checked exclusion leaves the completed and conditional comparisons at 235 and 234. Four local
selected sets have been independently checked; they rule out several
stronger local claims, without constructing complete snakes.

The outer-count-sum-22 hypothesis has a complete native sorted-input LRAT,
but its concrete semantic proof, Lean replay and actual-snake transfer
remain pending. Earlier unsorted attempts timed out. See their exact
records before continuing; do not restart them automatically.

- `lean/MiddleCount111.lean`: the actual-snake restriction and graph guards.
- `lean/Refined111/`: final checked contradiction and semantic modules.
- `lean/CounterSound111.lean`: checked generic soundness with explicit counter bounds.
- `data/refined-plan.json`, `logs/`, `data/*-audit.json`: exact final proof evidence.
- `data/probes/`, `data/witness-audit.json`: bounded probes and independent local-witness checks.
- `data/middle325-profiles/`: numerical effect of the proved interval exclusion.
- `data/sum22-profiles/`: explicitly conditional sum/excess experiment.
- `data/sum21-sorted-core.json`, `work/sum21-sorted/`: native sorted sum certificate.
- `data/large-artifact-archives.json`: lossless archives of large proof files for Git transport.

The earlier `generated-middle/` and `lean/Recovered111/` exports are
preserved intermediate stages, without final compiler receipts. The
refined proof is the one listed in the final plan. Large raw proof files
remain locally; their verified gzip copies are the repository artifacts.

Milestone 104 continues its original potential batch. The paper remains
revision 106, with the next full revision scheduled for 116. The remaining
reference union has 1,366 unresolved entries. The full research goal remains
active and no improved global upper bound is claimed.

The final conditional family experiment raises the completed-profile mean
from 483 to 3384/7, with potential range 3860/7. Its integer comparison remains 235;
the conditional-profile comparison remains 234. The new completed obstruction
is a fourteen-edge cycle. See `data/family-profiles/results.json`.
