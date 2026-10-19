# Targeted mergers from the seven-component state

Checkpoint: 18 October 2026. No new snake witness or further component merger
was obtained. The target remains 196 edges; this milestone investigates
constructive restrictions, not a global upper bound.

## Model and results

The input is milestone 14's 197-vertex state: a 40-edge path and six 26-cycles.
Both accumulated cycle exclusions are retained. Freeze all but one or two
cycles, forbid their closed neighborhoods to the new path, and replace the old
path plus the released cycles by one connected induced path. Both endpoints
are free. The required replacement lengths are 66 or 92 edges.

| Released cycles | Retained old path | Result | Time limit |
|---|---|---|---:|
| 0 | All 41 vertices | INFEASIBLE during presolve | 60 seconds |
| 0 | Unrestricted | UNKNOWN | 60 seconds |
| 0 and 1 | Unrestricted | UNKNOWN | 60 seconds |
| 0 and 2 | Unrestricted | UNKNOWN | 60 seconds |

Here the first column lists cycle indices, not their number. Releasing path
vertices 17 alone, 116 alone, both, or the five vertices 17, 116, 90, 72, 89
while retaining the rest also gave restricted INFEASIBLE results during
presolve. These exclusions are solver evidence without Lean certificates.

The preserved-path obstruction has a direct finite diagnostic. With the five
other cycles frozen and the internal path vertices retained, endpoint 120 has
no legal first extension. Endpoint 0 can reach only vertex 2, and that vertex
has no further available continuation. The relaxed reachable addition set is
therefore {2}, while the merger needs 26 added path vertices. The exact sets
and candidate blockers are in `data/endpoint-diagnostic.json`; this diagnostic
is independently computed, not a Lean-certified global claim.

## Controls and cut accounting

The latest saved state violates the most recently added cycle exclusion by
design: that cut asks the next solver round to change the state. Freezing all
its cycles while retaining that pending cut must therefore fail. The negative
control records this failure. A separate positive control removes the pending
cuts, freezes the six cycles, and independently recovers a valid 40-edge path.
The positive control is not used as a construction result.

For a cycle set $C$, frozen vertices $F$, and changing path vertices $R$, the solver
imposes the signed constraint

$$|C\cap R|\le |C|-1-|C\cap F|.$$

`lean/FrozenCycleCuts.lean` proves its equivalence to the full cycle exclusion
when F and R are disjoint. It also proves that a fully frozen cycle makes this
constraint impossible. Integer subtraction matters: a negative right-hand
side must not be truncated to zero. Both audits passed with standard axioms.

## Reproduction and scope

Use the dependencies and runtime versions from milestone 14. From the root:

```sh
python milestones/15-component-mergers/scripts/merge_components.py --cycles 0 --seconds 60 --output milestones/15-component-mergers/data/new-run.json
python milestones/15-component-mergers/scripts/endpoint_diagnostic.py
python milestones/16-cycle-reservoirs/scripts/verify_checkpoint.py
```

`--keep-path` fixes the current path vertices; `--release-path-vertices` lists
exceptions. The original source snapshot preserves the hashes of early runs.
The checkpoint verifier covers both this milestone and milestone 16, checks
saved feasible paths and source identities, and audits the Lean logs. It does
not convert solver infeasibility into a proof.

The restricted failures motivate a different starting configuration with more
initial vertices. [Milestone 16](../16-cycle-reservoirs/README.md) investigates
this direction and prepares a cell-based construction model.
