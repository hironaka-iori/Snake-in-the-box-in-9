# Recombination with a common endpoint pair

Checkpoint: 20 October 2026. Target: 196 edges. No witness longer than 191
edges was found. This is a completed construction experiment, not a solution
of the global problem.

## Exact segment searches

The recipient is the milestone 19 snake with 186 edges, oriented from 41 to
67. The donor is milestone 20's Lean-checked 190-edge path with those endpoints.
The difference word 106 has weight four. Permuting its four set coordinates
and five unset coordinates gives 2,880 endpoint-fixing cube isometries.
Translation by 106 swaps the endpoints; reversal restores the orientation.
Both cases give 5,760 alignments.

The single-segment census checks every pair of shared anchors, in either
donor order, with positive length gain. An adjacent recipient anchor pair
cannot accept a nonempty interior because its existing edge becomes a chord.
Closed-neighborhood bit masks test distinctness and all cross-adjacencies.
There were 7,232,848 remaining candidates and 5,760 accepted exchanges.
Every accepted exchange replaces the entire recipient with the donor.
No partial positive exchange survived. `verify.py` independently rechecks
twenty evenly spaced alignments by direct unordered-pair testing.

Twelve alignments were selected for further searches: the six largest
overlaps, followed by six positions evenly spread through the remaining
overlap ranking. They have union sizes 272 through 325. The two-segment
census permits cuts sharing a boundary anchor, but their deleted interiors
are disjoint. Individual gains may be negative; their sum must be positive.
It tests 104,649 positive-gain pairs. All 1,305 accepted results are again
the twelve aligned donors. Every accepted result was independently checked.
These are ordinary finite computations, not Lean-certified exhaustive proofs.

## Arbitrary union searches

The model permits any induced-path ordering within the union and fixes only
the endpoints to 41 and 67. Parent controls at lengths 186 and 190 passed.

| Additional constraint | Target | Runs | Outcome |
|---|---:|---:|---|
| Retain every shared vertex | 196 | 12 | INFEASIBLE |
| Shared vertices may be removed | 196 | 12 | UNKNOWN |
| Shared vertices may be removed | 192 | 12 | UNKNOWN |

Each run used a six-second limit, two workers and random seed 196. Solver
exclusions are restricted to the stated union and have no Lean certificates.
UNKNOWN does not exclude a witness.

Three 30-second optimization runs at length 190 maximize the smaller of the
numbers of selected vertices exclusive to each parent. Each returned the
donor, with objective zero and a positive unresolved objective bound. Thus
the experiment found no mixed 190-edge seed; it did not prove none exists.
`propagate.py` is a control: degree propagation while retaining the intersection
cannot remove any union vertex, since each entire parent remains feasible.
This prevents attributing the solver exclusions to elementary degree peeling.

## Lean evidence

`lean/Join.lean` constructs an induced path by joining two paths when all
cross-equalities are excluded and the only cross-adjacency is the joining
edge. The start and end identities are proved. The fourth audit checks the
factorial count. All four passed on Lean 4.19 with pinned mathlib; three use
only propext, Classical.choice and Quot.sound, and the arithmetic theorem
uses no axioms. The enumerations and solver results are outside these proofs.

Use the runtime and dependency paths recorded in milestone 20. Compile from
the pinned mathlib directory with `lake env lean` and the existing core
`Snake9.olean` on LEAN_PATH. The successful receipt is `logs/join.log`.

Run scripts from the repository root:

```sh
python milestones/21-endpoint-recombination/scripts/exchange.py
python milestones/21-endpoint-recombination/scripts/union_search.py
python milestones/21-endpoint-recombination/scripts/double_exchange.py
python milestones/21-endpoint-recombination/scripts/diversify.py
python milestones/21-endpoint-recombination/scripts/propagate.py
python milestones/21-endpoint-recombination/scripts/verify.py
```

## Collaborator integration

GitHub main initially remained at 8ec25ecc. The branch
`research/unconditional-241` advanced to ddf2b4f9. It contains successful
receipts for the unconditional 238 theorem, from commits c45ffa76 and
5c55ddd5. The relevant final theorem, bridge, aggregation, clause-soundness
assembly and generated refutation sources already agree with this checkout.
The three Linux receipts were imported without replacing local research or
manuscript settings. The manuscript and README now state 191 <= a(9) <= 238.

This round inspected the source connection and receipts; it did not rebuild
the full proof closure. The collaborator's final audit uses an incrementally
built Linux library. A fresh independent source rebuild remains pending.
The other active branch, `claude/relaxed-keller-60ks7i`, has further potential
evaluation and radius-four refinement work; no additional bound is adopted.
`othercontributors/` still contains the previously present DFS report.

The updated manuscript matches the existing editor mirror. Its three authors
and hyperlink/PDF metadata settings are preserved. The built-in compiler
failed before compiler execution with the Windows split-writable-root error;
no successful PDF build or visual inspection is claimed.

## Next construction experiment

The tested recombination family repeatedly recovers its donor. Use complete
191-edge donors whose endpoints need not match the recipient pair. Start by
extending the current 190-edge donor by the last vertex of its source witness,
then allow cuts at shared internal anchors. Preserve the exact pairwise
acceptance test and seek 196 directly. The extra donor vertex and released
endpoint alignment are changes to the search family, without a claim that
they suffice. Global upper-bound research remains with collaborators.
