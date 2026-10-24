# Six-count state model and common excess accounting

The finite graph has exact normalized minimum cycle mean **42/11**. An eleven-edge cycle attains the value, and a saved integer potential proves the matching lower bound on all 4,561,226 retained edges. This result concerns the specified finite graph. It gives no new global snake bound or snake construction.

The graph records seven normalized directions and six clamped counts, with 34 * 6^6 = 1,586,304 states. Symbol 6 retains the interval [6,21]. It uses the 732-window catalogue and the identified proved restrictions from milestones 28, 31, 32 (only four replayed cases), 33, 36, 38, 40, and 41. It does not assume the unproved universal six-fours exclusion.

For each seven-centre window, D is the maximum of available excess demands. Each demand is at most the excess sum on that window, so the maximum has the same upper bound. A path position belongs to at most seven such windows. With C counting the forward share-bonus occurrences once, the weight is 168 b + 24 D + 42 C. Three Lean audits establish the seven-window budget, maximum rule, and combined charge arithmetic. The complete graph-to-snake bridge remains pending.

All eleven windows of the attaining cycle are UNSAT in the stronger radius-four seven-centre solver model. These screens have no replayed proof certificates here. They identify candidates for additional exclusions; they do not justify removing those edges from the proved restriction family.

## Reproduction and verification

- `scripts/model.py`: reconstruct the graph; the generated graph is ignored under `build/`.
- `scripts/analyze.py`: find a candidate cycle and generate an integer potential certificate.
- `scripts/check.ps1`: compile the common-budget lemmas against the existing milestone 41 support.
- `scripts/verify.py`: independently verify the saved arrays, every potential inequality, cycle closure and exact mean, and Lean axiom audits. It does not invoke the optimizer.
- `scripts/screen_cycle.py`: repeat the numerical local screens.

The potential satisfies 7056 + pi(v) <= 11 w(u,v) + pi(u) and has range 8064. Summing on any cycle proves mean w >= 7056/11; dividing by 168 gives 42/11. The recorded eleven-edge cycle has zero demand and share corrections and count sum 42, establishing equality. The verifier checks the saved finite object, rather than a complete Lean verification of graph enumeration.

The most useful next step is to replay a small, general exclusion from the eleven rejected seven-centre windows and rebuild the graph. Increasing bonuses on patterns absent from this cycle cannot exclude it.
