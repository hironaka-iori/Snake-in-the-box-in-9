# Contracted fixed-path search

Checkpoint: 20 October 2026. No improved snake was found.

## Construction hypothesis

Contracting fixed outside path components may make coordinate-face repair more tractable while preserving the expanded length objective. Any verified length above 191 is useful; this experiment imposes no single exact improvement target.

For a free region U and seed S, the selected vertices outside U remain exactly S minus U. Their induced components are paths. Remove their internal vertices from the solver and forbid every candidate inside vertex adjacent to a removed vertex. Replace each component with at least three vertices by a mandatory connection between its retained endpoints. Components of one or two vertices remain unchanged.

If c retained vertices are selected and r fixed internal vertices were removed, the expanded snake has c+r-1 edges. The solver maximizes this quantity. The fixed 191-edge seed supplies both a feasibility control and a complete hint.

## Mathematical checks

`lean/Rigidity.lean` proves five results: an injective sequence of integer positions with unit steps has constant direction; an adjacent embedding in a snake has that property; a selected subpath is contiguous in either direction; the expanded edge-count identity; and the impossibility of closing an injective unit-step chain of at least three positions. All five axiom audits passed with only `propext`, `Classical.choice`, and `Quot.sound`.

The manuscript gives the contraction argument. The full Python model, expansion correspondence and optimizer are not certified in Lean. The general graph contraction argument remains a written proof supported by the checked contiguity and counting results.

## Experiments

The seed is milestone 18's aligned 191-edge bank example. The ten Q8 faces and their component inventory are inherited from milestone 23.

| Model | Small-cube oracle comparisons | Q9 runs | Best expanded length |
|---|---:|---:|---:|
| Contracted circuit model | 592 passed | 10 | 191 |
| Added edge linearization and short-cycle cuts | 592 passed | 10 | 191 |

Each Q9 run used two workers, random seed 192 and a 20-second limit. Each was preceded by a separate fixed-seed control, which returned OPTIMAL at 191. All twenty unrestricted optimization runs returned FEASIBLE at 191. None proved optimality. Their weak objective bounds are restricted solver bounds and do not supersede known global theorems.

The strengthened model adds explicit upper bounds on selected edge variables, the path edge-count equality, and 193 to 551 triangle or four-cycle inequalities in the contracted graph. Artificial connections are included, so a cut can exclude a cycle whose expansion contains a long fixed outside segment. These are redundant constraints; this short comparison found no construction gain.

The independent subset oracle exhausts all induced path vertex sets in Q2, Q3 and Q4. The region scenarios cover all regions of one Q2 seed, all regions of two Q3 seeds, and 64 deterministic regions of one Q4 seed. Each model is compared with that oracle in 592 cases. These are finite controls, not a proof for arbitrary dimension.

`scripts/verify.py` independently checks all unordered pairs of the 40 saved paths, their outside membership, fixed component edges, removed vertices and length offsets. It also checks source hashes and the five Lean audit lines. `verification.json` records the evidence.

## Reproduction

From the repository root, with the project Python dependencies:

```text
python milestones/24-contracted-face-search/scripts/small_controls.py
python milestones/24-contracted-face-search/scripts/contracted.py --seconds 20 --output milestones/24-contracted-face-search/data/max-search.json
python milestones/24-contracted-face-search/scripts/strengthened.py --seconds 20
powershell -File milestones/24-contracted-face-search/scripts/check_lean.ps1
python milestones/24-contracted-face-search/scripts/verify.py
```

The commands overwrite their named experimental records. Preserve existing records before new runs. The Lean runner documents this workstation's pinned dependency paths.

## Collaborator refresh

GitHub main remained at 02adada5 during the initial refresh. The branch `research/unconditional-241` advanced to 2a7fe4e4, reporting the completed 237 theorem and successful final axiom audit. Its receipt records 17,197 replay modules and 387 retained windows; the final chain uses an incrementally built library. The receipt also preserves earlier failed attempts before successful completion. This round inspected the final audit and report but did not import or rebuild that source closure. Main's integrated theorem remains 238; the stronger collaborator result is recorded separately.

The other active branch advanced to 73ce64d9 with seven-centre refinement work. The new `research/empty-square-tradeoff` branch records a finite saturated-face pair classification. These are separate upper-bound investigations.

## Next construction step

Search for alternative 191-edge fillings with a changed selected vertex set, then run other coordinate-face repairs from those seeds. This releases the outside pattern indirectly between iterations. Record diversity as an intermediate outcome only; it gives no numerical improvement until a longer induced path is independently verified.
