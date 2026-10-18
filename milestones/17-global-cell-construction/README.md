# Global cell construction and palette diagnosis

Checkpoint: 18 October 2026. Target: a single 196-edge snake. No improved
lower-bound witness was found. This milestone investigates construction;
it does not pursue a global upper bound.

## Model and controls

`scripts/search.py` permits all sixteen cells to change together. The allowed
vertices are A union U in even cells and B union U in odd cells, using the
saved milestone 16 base sets. Direct selected-degree constraints implement
the local tables without expanding sixteen copies of their 4,973 rows.
There are exactly two endpoints and, for feasibility runs, 197 vertices.
Every saved solution is checked against the local tables.

The local tables contain ten distinct cyclic components per cell type.
Their 160 translated cuts are checked in `lean/LocalCycles.lean` using the
original snake definition and the previously proved general cycle-cut lemma.
An optional circuit model enforces connectivity from the start.

| Run | Result |
|---|---|
| Fixed saved 197-vertex disconnected configuration, cycles allowed | Reproduced 28-edge path plus twelve 14-cycles |
| Same configuration, local cycle cuts enabled | Rejected |
| Same configuration, circuit connectivity enabled and local cuts disabled | Rejected |
| Fixed connected 28-edge path | Accepted |
| All cells variable, 196 edges, local cuts | UNKNOWN after 120 seconds |
| All cells variable, 196 edges, circuit connectivity | UNKNOWN after 120 seconds |
| Maximize connected path, starting with the 28-edge control | FEASIBLE, 101 edges after 120 seconds |

The 101-edge path passed all pairwise adjacency checks. It is a construction
control, below the known 191-edge witness. Solver timeouts do not establish
infeasibility. The source snapshot preserves the driver used by the first
six runs; the growth run uses the maintained driver.

## Why this palette should be enlarged

`scripts/audit_capacity.py` independently enumerates every subset using an
edge-list degree calculation and disjoint-set cycle detection. It reproduces
all 4,973 rows of each prior table exactly. Exactly 4,142 states per type are
acyclic. The maximum selected size is 10, 14, or 14 when the number of
nonconnector internal endpoints is zero, one, or two, respectively.

Thus each enumerated acyclic state satisfies c <= 10 + 4e. A nonconnector
cannot have an external neighbor under this palette. In a single path,
the sum of these endpoint counts is at most two. Across sixteen cells,
the census therefore permits at most 160 + 4*2 = 168 selected vertices.
The target requires 197 vertices. This is a diagnosis of an overly
restrictive construction family, not evidence against the conjecture 196.

`lean/Capacity.lean` checks the numerical profiles and the conditional
summation deduction. Enumeration completeness and its geometric
interpretation have not been proved in Lean. The seven theorem audits in
this milestone use only standard axioms, or no axioms.

## Next constructive step

Permit selected vertices from the opposite base cycle in each cell.
Such vertices allow new cross-cell adjacencies outside the four shared
connectors. First allow a small number of these additions, preserve the
general induced-path conditions and valid cycle cuts, and validate against
existing known paths. Do not spend further 196-edge searches within the
unchanged four-connector palette.

## Reproduction and evidence

Run from the repository root, with the Python runtime and OR-Tools setup
recorded in the prior milestones:

```sh
python milestones/17-global-cell-construction/scripts/audit_capacity.py
python milestones/17-global-cell-construction/scripts/verify.py
python milestones/17-global-cell-construction/scripts/search.py --connected --maximize --seconds 120 --hint milestones/17-global-cell-construction/data/path-control-input.json --output milestones/17-global-cell-construction/data/new-growth.json
```

The first command regenerates the capacity JSON and Lean source. Compile
both Lean modules with the pinned Lean 4.19/mathlib environment from milestone
14 before running the verifier. `data/verification.json` records source and
result hashes normalized to LF. The verifier checks witnesses, cell masks,
components, all recorded cuts, source versions, and all seven Lean audits;
it does not turn solver exclusions into proof certificates.

At the start of this round, origin/main matched the local published commit.
Collaborator branches advanced KEEP96 proof batching/checkpoint recovery,
upper-bound build resumption, 2423 RUP splitting, and an empty-square-aware
local-weight oracle. These branch developments were inspected, not merged
or independently rebuilt in this construction round.
