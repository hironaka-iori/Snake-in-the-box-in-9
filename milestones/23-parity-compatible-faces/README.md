# Parity-compatible construction targets and larger regions

Checkpoint: 20 October 2026. Any verified improvement above 191 is valuable.
No improved witness was found in this round.

## Target selection

A snake longer than 191 has a 192-edge prefix. However, a path with the same
endpoints as a 191-edge snake must have odd length. The smallest possible
improvement retaining those endpoints therefore has 193 edges.

Lean checks the equivalence between existence of any improvement and a
192-edge snake, the 193-to-192 prefix construction, and the necessary odd
length/minimum 193 condition for improvements with the original endpoints.
This does not assert that every longer fixed-endpoint path yields a
193-edge path with those same endpoints.

The search source is milestone 18's aligned bank-129 witness. The established
full-cube path model permits arbitrary ordering and changes within the free
region. Every selected and unselected vertex outside that region remains fixed.
The endpoints are not explicitly fixed; they may move when the model permits.

## Completed searches

| Region family | Exact target | Outcomes |
|---|---:|---|
| All 672 coordinate Q6 faces | 193 | 672 INFEASIBLE |
| All 144 coordinate Q7 faces | 193 | 142 INFEASIBLE; 2 UNKNOWN at 2 seconds |
| Q7 retries, indices 0 and 3 | 193 | Index 3 INFEASIBLE; index 0 UNKNOWN at 30 seconds |
| All 1,008 opposite Q5 cell pairs | 193 | 1,008 INFEASIBLE |
| All 18 coordinate Q8 faces | 192 | 8 INFEASIBLE; 10 UNKNOWN at 5 seconds |
| All 18 coordinate Q8 faces | 193 | 8 INFEASIBLE; 10 UNKNOWN at 5 seconds |

Each pair of opposite Q5 cells has 64 vertices. The two cells differ in all
four fixed coordinates, so their union varies all nine coordinates and is
not contained in any proper coordinate face. There are choose(9,5) * 8 =
1,008 such regions. A 191-edge positive control passed and was independently
checked. The full survey finished in about 49 seconds.

These are exact-length restricted solver results without Lean infeasibility
certificates. Infeasibility at 193 within a fixed region does not exclude a
195-edge solution in that same region: truncating it can alter the prescribed
outside vertices. UNKNOWN excludes nothing.

## Boundary preprocessing for the unresolved cases

The same ten Q8 faces remain unresolved at both targets. Their selected
outside vertices form disjoint fixed paths. Any internal vertex of one of
these paths already has two selected neighbors, so its other neighbors must
be absent. The fourth Lean theorem checks this exclusion rule.

`data/boundary-inventory.json` records the components and forbidden inside
vertices. The smallest proposed contracted model is face 3: 99 fixed outside
vertices in two paths, of which 95 are internal; after removing their forbidden
inside neighbors, 161 inside vertices and four outside endpoints remain.
This would give a 165-vertex model instead of the original 512-vertex model.
The other unresolved models would have 166 through 212 vertices.

The next task is to implement and validate this contraction, expand every
accepted result back to Q9, and maximize length rather than requiring one
exact target. That allows the solver to retain a 191-edge control while
seeking any longer path. The contraction model is not yet implemented or
certified; the current inventory is a preparation step only.

## Reproduction and audit

From the repository root:

```sh
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 6 --edges 193 --seconds 1 --output milestones/23-parity-compatible-faces/data/faces6-193.json
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 7 --edges 193 --seconds 2 --output milestones/23-parity-compatible-faces/data/faces7-193.json
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 7 --indices 0,3 --edges 193 --seconds 30 --output milestones/23-parity-compatible-faces/data/faces7-193-retry.json
python milestones/23-parity-compatible-faces/scripts/opposite_cells.py --output milestones/23-parity-compatible-faces/data/opposite5-193.json
python milestones/23-parity-compatible-faces/scripts/opposite_cells.py --edges 191 --total 10 --output milestones/23-parity-compatible-faces/data/opposite5-control191.json
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 8 --edges 192 --seconds 5 --output milestones/23-parity-compatible-faces/data/faces8-192.json
python milestones/19-coordinate-face-repair/scripts/search_faces.py --dimension 8 --edges 193 --seconds 5 --output milestones/23-parity-compatible-faces/data/faces8-193.json
python milestones/23-parity-compatible-faces/scripts/boundary_inventory.py
python milestones/23-parity-compatible-faces/scripts/verify.py
```

Compile `lean/Targets.lean` using milestone 22's `scripts/check_lean.ps1`.
All four audits passed with only standard axioms. The verification script
checks region coverage, source hashes, controls and boundary decomposition;
it does not upgrade solver statuses to mathematical exclusions.
