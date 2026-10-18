# Coordinate-face replacements and two-arm construction

Checkpoint: 19 October 2026. Target: a 196-edge snake. The best established
lower bound remains 191 edges. Solver exclusions below are restricted and
have no Lean infeasibility certificates.

## Broader replacement regions

The input is milestone 18's aligned bank entry 129. The face search fixes
membership of every vertex outside the released coordinate face and uses
the existing full-cube connected induced-path model inside it. Cloning the
base model avoids rebuilding its arcs for every face. A 191-edge control
passed, including independent pairwise witness verification.

| Released region | Target 192 | Target 196 |
|---|---|---|
| All 672 six-dimensional coordinate faces | 672 INFEASIBLE | 672 INFEASIBLE |
| All 144 seven-dimensional faces, 2 seconds each | 142 INFEASIBLE, 2 UNKNOWN | 142 INFEASIBLE, 2 UNKNOWN |
| Retry the two unresolved faces, 60 seconds each | 1 INFEASIBLE, 1 UNKNOWN | 1 INFEASIBLE, 1 UNKNOWN |

The remaining face fixes bits 7 and 8 to zero. Its 50 selected vertices are
the first 50 vertices of the seed; the other 142 selected vertices form a
single path. The other unresolved face was discharged by the longer solver
run. These results concern this seed and the specified face restrictions.

## Lean geometry

`lean/FaceRepair.lean` proves that membership agreement outside a region is
equivalent to containing the symmetric difference in that region. For a
nonempty change set, containment in some six-dimensional coordinate face
is equivalent to variation in at most six coordinates. The proof also
checks the arithmetic counts 672 and 144. Eight axiom audits pass with only
standard axioms. Face enumeration is audited independently in Python;
the solver models and their exclusions are not Lean-certified.

## A smaller constructive problem

For the remaining face, the two possible attachments to the fixed outside
path are 53 and 44. Forbidding neighbors of the outside path's interior
leaves 78 available vertices and 147 cube edges. The two-arm model seeks
two mutually nonadjacent induced paths, one attached at each endpoint.
It replaces the fixed 142-vertex path temporarily by an artificial edge
between 53 and 44. Every feasible result is expanded and checked in Q9.

The two arms need 55 selected vertices for 196 edges, or 51 for 192 edges.

| Experiment | Result |
|---|---|
| Two selected attachment vertices, expanded control | Valid 143-edge path |
| Target 196 | INFEASIBLE after about 25 seconds |
| Target 192 | UNKNOWN after 60 seconds |
| Maximize length, cap 196, 120 seconds | FEASIBLE, 186 edges |

The 186-edge construction uses 45 face vertices and the 142 fixed vertices.
Its endpoints are 67 and 41. Its compressed path passes through the
artificial edge in reverse orientation; the expansion uses the reversed
outside path accordingly. All pairwise checks pass.

`data/two-arm-seed186.json` is the reusable seed. A canonical transition
comparison found no equivalent contiguous 186-edge subpath in the 131
stored witnesses, allowing translations, coordinate permutations and path
reversal. This is a finite-bank diversity result, not a length record or a
claim of novelty in the literature.

The next construction search should release vertices of the formerly fixed
middle path as well. Repeating a 196-edge search with that same two-arm
restriction is not the priority after its solver exclusion.

## Reproduction

Run from the repository root with the established Python and OR-Tools setup:

```sh
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 6 --edges 196 --output milestones/19-coordinate-face-repair/data/new-faces6.json
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 7 --edges 192 --seconds 60 --indices 0,3 --output milestones/19-coordinate-face-repair/data/new-faces7.json
python milestones/19-coordinate-face-repair/scripts/two_arms.py --maximize --seconds 120 --output milestones/19-coordinate-face-repair/data/new-growth.json
python milestones/19-coordinate-face-repair/scripts/verify.py
```

Compile `lean/FaceRepair.lean` from the pinned mathlib working directory,
using the same Lean 4.19 dependency paths as the prior milestone. Its
successful receipt is `logs/face-repair.log`. Source snapshots retain the
versions used before targeted retries and length maximization were added.
The independent verifier checks face coverage, source hashes, all witnesses,
the compressed graph and expansion, bank-subpath comparison, and eight
Lean audits. It does not turn solver INFEASIBLE into a proof certificate.

## Collaborator update

The fetched `research/window-244` branch at `2fbca375` contains an independent
source-reconstruction receipt for the interval 191--241, including 4,457
modules and standard-axiom final audits. Its receipt and final axiom log
were inspected, without merging or rebuilding them in this construction
round. Other branches advanced proof-generation and verification work.
The exact reviewed heads and receipt are saved in `data/collaborator-review.json`.
