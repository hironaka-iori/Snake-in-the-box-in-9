# Construction through a path and cyclic components

Checkpoint: 18 October 2026. Target: a 196-edge snake. The checked construction
below is disconnected and gives no improved snake lower bound.

## Mathematical search space

Select 197 vertices in Q9. Exactly two selected vertices have selected degree
one, and every other selected vertex has selected degree two. Such a finite
graph consists of one path and zero or more cycles. The solver does not retain
a bank prefix. An endpoint is translated to zero and its neighbor is mapped
to one by a coordinate permutation.

When a candidate has a cyclic component C, add the constraint that at most
|C|-1 of its vertices remain selected. The existing `CycleExclusion` theorem
proves that no induced path can contain a nonempty vertex set with two distinct
neighbors at every vertex. `lean/CycleCuts.lean` derives the exact cardinality
inequality used here and connects it to the existing Boolean cycle checker.
Its three Lean axiom audits passed using only the standard foundations.

All coordinate-square cuts can be included initially. This removes 4-cycles
but still permits longer cyclic components. Every accepted single path is
independently checked by all vertex pairs before being reported as a witness.

## A concrete 197-vertex starting state

A small solver found two disjoint 26-vertex sets in Q6, each inducing a
26-cycle. Place the first set in each even-parity layer of Q3 x Q6 and the
second in each odd-parity layer. Since the base sets are disjoint, there are
no edges between different layers. The result has eight disjoint 26-cycles,
208 vertices, and 208 edges. Delete eleven consecutive vertices from one
cycle, then normalize one endpoint and its neighbor.

The saved seed has:

- 197 distinct vertices and 196 induced edges;
- one path on 15 vertices, hence 14 edges;
- seven induced cycles on 26 vertices each;
- endpoints 0 and 39, with the neighbor of 0 equal to 1.

An independent Python audit checked all 19,306 unordered vertex pairs, the
component partition, and the ordered path. The generated Lean certificate
checks the vertex count, distinctness, selected degrees, partition, and validity
of the seven cycle cuts. The certificate passed Lean; all eight audited
declarations across the two modules use only standard axioms. The log and
verification manifest record the exact scope. Connected component sizes and
the ordered 14-edge path were checked independently in Python.

This seed is a disconnected intermediate state. Its 196 total edges are not
a 196-edge snake. No novelty claim is made for the product principle or the
component relaxation.

The published 208-edge product in Orland et al. is a union of **paths**, with
224 vertices, and is different from this cycle construction. The distinction
was checked against [Section 3 of the paper](https://arxiv.org/html/2607.15270v3).
No published snakepit was assumed to be a union of cycles.

## Completed searches

| Run | First candidate | Outcome |
|---|---|---|
| Fixed 191-edge bank control | One path | Independent witness check passed |
| Q4, seven-edge control | One path | Independent witness check passed |
| Q9, 196 edges, square cuts | None within 20 seconds | UNKNOWN |
| Same, hinted by a six-chord walk | None within 20 seconds | UNKNOWN |
| Same, without initial square cuts | None within 20 seconds | UNKNOWN |
| Same, hinted by the new product seed | One path and seven cycles | Seven cuts added; next round UNKNOWN after 20 seconds |
| Same seed, one nearest cycle cut per round | One path and seven cycles | Next candidate has one 40-edge path and six 26-cycles; following round UNKNOWN |

Runs had a 60-second total budget and a 20-second per-round budget, stopping
at the first unresolved round. They did not all use 60 seconds. The new seed
led to a first-round candidate with the same component sizes, differing by five
selected vertices; the total seeded run took about 20.36 seconds.
The sequential-cut run accepted its next candidate in about 0.93 seconds by
replacing five vertices from the preceding solver candidate (eight net replacements
from the original product seed). It retains 197 vertices and 196 total edges, but still
has seven components. `data/improved-seed.json` preserves this configuration,
its independently checked 40-edge path, and both cycle exclusions accumulated
so far. No impossibility conclusion follows from any UNKNOWN result.

## Reproduction and verification boundary

Python 3.12+, OR-Tools 9.15.6755, and the existing search dependencies are used.
From the repository root:

```sh
python milestones/14-component-construction/scripts/product_seed.py
python milestones/14-component-construction/scripts/verify_seed.py
python milestones/14-component-construction/scripts/component_search.py --edges 196 --seconds 60 --round-seconds 20 --hint milestones/14-component-construction/data/product-seed.json --output milestones/14-component-construction/data/new-product-run.json
python milestones/14-component-construction/scripts/verify_results.py
```

Preserve existing results before rerunning the seed generator. Two-worker
solver scheduling can produce different base cycles. The saved sets and
checks are the authoritative evidence for this run.

Lean uses version 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. It reuses the checked core and
`CycleExclusion` library from the window-support build. Add those library
directories and this milestone's ignored `build/` directory to `LEAN_PATH`.
From the pinned mathlib directory, compile `lean/CycleCuts.lean` with
`lake env lean --root=<absolute lean directory> -o <absolute build/CycleCuts.olean>`
and the absolute source path, then check `lean/SeedCertificate.lean` with
`lake env lean`. The seed certificate is regenerated by `verify_seed.py`.

The older driver snapshots in `scripts/snapshots/` preserve the exact source
hashes recorded by the initial controls and pilots. They are provenance
snapshots, not additional maintained entry points. The maintained driver adds
support for a vertex-set hint and `--one-cut`; the selected-degree constraints
are unchanged.

The general cycle-cut inequality is Lean-checked. This does not verify the
entire solver encoding, its symmetry reduction, or practical convergence.
The explicit seed and returned control witnesses have independent checks.

## Next constructive step

Adding all seven cycle cuts simultaneously demands changes in every cyclic
component. Sequential cuts completed one component merger in this pilot,
while simultaneous cuts did not produce a next candidate within the same
per-round budget. This is one comparison, not a general performance claim.
The next step is to resume the seven-component state while retaining both
previous cuts, then test further component mergers. The 197-vertex target
remains fixed; no claim that all remaining cycles can be eliminated follows.
