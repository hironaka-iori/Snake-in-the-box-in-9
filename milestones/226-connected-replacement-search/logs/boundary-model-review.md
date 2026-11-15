# Round 226 boundary-cut model review

Conclusion: the actual width-44 worker correctly implements the reviewed necessary boundary-omission condition and the optional same-face capacity condition. No unintended fixed crossing allocation or invalid exclusion was identified. The terminal run covers all 92 requested contexts, excluding 46 natively and leaving 46 unknown.

## Read scope and input family

Read all 91 lines of `scripts/joint_boundary.py` and all 58 lines of `scripts/run_boundary.py`, together with their complete diffs from the reviewed split worker and wrapper. Read `data/boundary44-plan.json`, the execution arguments, and the closure dependencies. The mathematical trimming implication was reviewed separately in `logs/coverage43-review.md`.

The copied `data/regions44.json` is byte-identical to milestone 224's original contact-free width-44 input. Its seed and appended endpoint agree with the width-43 source used by the complete cover. All 92 distinct requested IDs exactly match the old width-44 unresolved list. The plan's parent pin matches milestone 224's `combined44.json`. These are 92 selected contexts from the 301-context family; the worker does not claim to search all 301 anew.

## Boundary selectors

For each block, the worker creates one Boolean selector. If that selector is true, each original boundary-adjacent vertex present in that block's domain is forced unselected. The Boolean OR of the two selectors requires at least one selector to be true. Thus at least one block omits both of its own boundary-adjacent vertices, exactly as required by the reviewed width-43 trimming argument.

The one-way implications are sufficient. Any valid candidate satisfying the necessary omission condition can set a corresponding selector true and the other false. Reverse implications are unnecessary. A boundary vertex absent from the domain is already omitted; skipping its equality adds no restriction. If both boundary vertices are absent, that selector may be chosen true without extra constraints. The code does not require both blocks to omit both vertices.

The assertion that each interval has 44 edges matches the current input and the proved trimming step. The selected-vertex interpretation relies on the existing selected anchor degree-one rows and actual-path inducedness, as explained in the preceding coverage review.

## Same-face capacity and crossing allocation

For a block whose anchors have equal coordinate-8 bits, a zero-crossing path would remain entirely in their face. If its prepared domain has fewer vertices in that face than the prescribed path size, such a path cannot exist. Its positive crossing count must be even, so imposing at least two is necessary.

The worker checks exactly equal anchor bits and strict face-size shortage, then adds `sum(edges) >= 2`. Its vertical-edge variables retain the Boolean product constraints, and the per-path parity equation remains present. A width-44 replacement requires 45 vertices. Independent recounting over the 92 requested contexts finds this additional inequality in 55 second domains and in no first domain. The other 37 second domains receive no such minimum from this rule.

The old first-crossing argument and equality are removed. Crossing allocations are therefore variable, subject to endpoint parity, any valid face minimum and the combined budget. In particular the worker does not force the first path to stay in the lower face. The remainder of the selected-degree, cardinality, cube-parity, cross-path compatibility, cycle-cut and final witness-audit code is unchanged in the complete diff.

## Closure dependency

Before building models, the worker requires `coverage43.json` to report `COMPLETE_NATIVE_EXCLUSION` and verifies every file hash in its saved pin map. The wrapper pins that coverage file, the input, both scripts and resource helper; it verifies those pins again before accepting a terminal process result. All current closure pins and wrapper pins match.

The width-43 exclusion is an explicit mathematical dependency of the boundary cut. Its inherited exclusions use already excluded older width-44 contexts; the new outcomes for the previously unresolved contexts are not dependencies of the width-43 cover. There is no circular use of these new boundary results. Native solver contradictions, concrete domain interpretation and finite coverage retain their separate verification limits. A status string and hashes alone are not a substitute for the independently reviewed cover argument.

## Terminal outcome audit

The worker was running during initial source inspection. Outcome inspection was deferred until its execution receipt became terminal. The final receipt is `ACCEPTED_NATIVE_RESULT`, exit code zero, no stop reason. The result reports `COMPLETE_COVERAGE`, exactly the 92 requested distinct IDs, 46 `INFEASIBLE`, 46 `UNKNOWN`, no witness, and no added cycle cuts. Recorded elapsed time is approximately 126.672 seconds.

Recomputed hashes match the saved script/input/coverage pins, every exported query model, the final result and both execution logs. This verifies the saved artifact associations; no optimizer rerun or independent contradiction replay was performed. Complete coverage means every requested context was queried. It does not change the 46 unknown outcomes into exclusions.

The remaining IDs are:

`19, 22–30, 56, 62–74, 105, 108–117, 191, 194–203`.

Together with the older 107 geometric and 102 native solver exclusions, the new 46 exclusions leave 46 open contexts among the original 301. The current width-44 family remains unresolved. No longer snake or global bound is obtained.

## Frozen hashes

| Artifact | SHA256 |
|---|---|
| `scripts/joint_boundary.py` | `186e13bbb73fd5bf9d96ccdcc364d45f1bc61df223fb3815baaf59383db41823` |
| `scripts/run_boundary.py` | `5bbd15df9b30bb2d9d212b76e8d2e2f4dfd9c367d2ff42927ecaa674f1fed406` |
| `data/regions44.json` | `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b` |
| `data/coverage43.json` | `440ea4f6766f0a4b8b7047e3fff8825e8ee25e1c248ecba97b4261a8bf00c74e` |
| `data/boundary44-plan.json` | `ac4ee66ac161afdf634cb12d9b8d75022c82b62585a0c51912716e0479a1a807` |
| milestone-224 `data/combined44.json` | `c4428697e1561f1c5f4e37928827322d59feed70b5df3bbf09dea0808dbbfb4d` |
| `data/boundary44.json` | `d4698f8d4ea7f652ee6759e76e3b469af0e463d5a38dc8bccc9029afd8e74ac4` |
| `data/boundary44-execution.json` | `630f6d0447d8c7394ebac664252e8b2a95de6c41501b46b8e476f83339e74985` |

No solver, compiler or software test was run by this reviewer. Only this requested log was written; all source, evidence and previous reviews were preserved.
