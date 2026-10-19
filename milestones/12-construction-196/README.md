# Constructive search targeting 196 edges

Checkpoint: 18 October 2026. No valid snake longer than 191 edges was found.

The target is the existing conjecture a(9) = 196. Its numerical motivation does
not establish existence or optimality. This milestone concentrates on finding a
witness; other collaborators are developing upper bounds.

## Method and checked acceptance rule

Search states are adjacent walks of exactly 196 edges. They may have repeated
vertices or forbidden chords. The defect score is four times the number of
repeated-vertex pairs plus the number of nonconsecutive adjacent pairs.
`lean/DefectCriterion.lean` proves that this score is zero exactly when the walk
is a snake, using the project's original definition. All three axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`; see
`logs/defect-criterion.log`. This checks the mathematical acceptance criterion,
not the C++ implementation or an existence claim.

`scripts/defect_search.cpp` exchanges two transition directions by translating
the intervening vertex interval, or changes one transition and translates the
whole suffix. Both operations keep consecutive vertices adjacent. Simulated
annealing permits temporary defects, and restarts use the 131 published bank
paths with short greedy extensions. Thus the interior and endpoints can change.
The implementation retains only strict improvements in the best score, which
limits diversity among equally good candidates. No novelty claim is made.

The separate audit run compared 104,939 evaluated mutation scores with direct
quadratic pair counts. Periodic checks also ran during the pilots. The saved
walks and every reported valid segment were independently recounted in Python.

## Completed experiments

| Target edges | Random seed | Proposals | Initial score | Best score | Duplicate pairs | Chords | Best valid segment |
|---|---:|---:|---:|---:|---:|---:|---:|
| 196 | 41 | 10,285,000 | 10 | 7 | 0 | 7 | 191 edges |
| 196 | 113 | 10,430,000 | 10 | 7 | 0 | 7 | 191 edges |
| 192 | 29 | 10,220,000 | 1 | 1 | 0 | 1 | 191 edges |

Each pilot ran for approximately 90 seconds. The 192-edge score of one already
occurs in the initial extension; it is not a search improvement. Seven chords
do not imply that seven local edits suffice to obtain a snake. The valid segment
record is maintained across the run and need not belong to the saved best walk.

Exact repair releases every position within a stated distance along the walk
from a defect, and the first and last ten positions. Other vertices must remain
selected, but their order is unrestricted. Both endpoints are free. The existing
connected induced-path model is reused; it does not fix the origin as an endpoint.

| Target | Seed | Radius | Fixed vertices | Result | Seconds |
|---|---:|---:|---:|---|---:|
| 196 | 41 | 4 | 145 | INFEASIBLE | 0.52 |
| 196 | 41 | 12 | 105 | UNKNOWN | 90.03 |
| 196 | 113 | 8 | 85 | UNKNOWN | 60.02 |
| 192 | 29 | 6 | 160 | INFEASIBLE | 0.22 |

A control fixing a known 191-edge path succeeded and its 18,336 unordered vertex
pairs were checked. INFEASIBLE concerns only the specified fixed vertex set;
these solver exclusions have no Lean certificate. UNKNOWN establishes neither
existence nor impossibility. Machine-readable inputs and outputs are in `data/`.
`data/pilot-summary.json` records independent checks and source hashes.
Hashes normalize CRLF to LF so a fresh Git checkout gives the same identity.
Repair records also preserve their original raw source hash as provenance.

## Reproduction

From the repository root, Python 3.12 or later:

```sh
python milestones/12-construction-196/scripts/audit_results.py
python -c "import json,pathlib; b=json.loads(pathlib.Path('work/bank9.json').read_text()); pathlib.Path('milestones/12-construction-196/data/bank-input.txt').write_text(''.join(' '.join(map(str,r['vertex_sequence']))+'\n' for r in b))"
```

Build the C++ file with a C++17 compiler and assertions enabled, for example:

```sh
g++ -O2 -std=c++17 milestones/12-construction-196/scripts/defect_search.cpp -o milestones/12-construction-196/build/defect_search
milestones/12-construction-196/build/defect_search --input milestones/12-construction-196/data/bank-input.txt --target 196 --seed 41 --seed-index 41 --seconds 90 --output milestones/12-construction-196/data/new-run.json
python milestones/12-construction-196/scripts/repair_walk.py --source milestones/12-construction-196/data/new-run.json --radius 12 --seconds 90 --output milestones/12-construction-196/data/new-repair.json
```

Create `build/` first. This Windows run used MSVC 19.44 with `/O2 /EHsc
/std:c++17`, without `NDEBUG`, and OR-Tools 9.15.6755 with two workers. Wall-time
stopping and parallel solver scheduling mean exact trajectories can vary.
Use new output names to preserve the saved pilot results.

For Lean, use Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build the shared core as documented at
the repository root. From the mathlib directory, add the compiled core library
directory to `LEAN_PATH` and run `lake env lean` on the absolute path to
`lean/DefectCriterion.lean`. The recorded check reused the already checked core
library from the strengthened-proof reproduction; it was not a new full core build.

The manuscript and existing editor source were synchronized with identical
hashes. The built-in LaTeX preview failed before compilation because of a
Windows sandbox configuration error; see `logs/latex-preview-status.txt`.
No successful PDF compilation or visual layout check is claimed for this update.

## Collaborator review and next direction

The synchronization integrated main through `807941e`, preserved the local
window-counter checkpoint `c63878c`, and published merge `e40b970`.

- KEEP=112 has a PASSED aggregate receipt for all 262 oriented bank entries.
  This excludes 192-edge regrowth retaining those particular initial segments;
  it supports moving beyond endpoint-only modifications. The receipt is
  `outputs/lean112/bank-proof.json`. It was inspected, not rebuilt in this round.
- The bounded KEEP=96 survey records 242 solver exclusions and 20 unresolved
  cases. Further Lean integration is on a separate collaborator branch.
- Main contains conditional bounds through 238. The separate branch
  `research/unconditional-241-only` at `890c486` contains an unconditional 241
  theorem and a saved successful audit with standard axioms. That branch was
  inspected but neither merged nor independently rebuilt here. Upper-bound
  development remains with those collaborators.

The next constructive experiment should preserve a diverse set of equal-score
walks, then replace several separated interior fragments together. The present
pilot repeatedly returns to one best walk, and merely releasing larger regions
produced unresolved models. A useful controlled comparison is conflict-focused
repair versus equally sized scattered interior releases, with the same solver
budget and independent witness check. This is a proposed experiment, not a
claim that it will reach 196. Multi-component layer constructions remain a
separate route if these walk searches stagnate.
