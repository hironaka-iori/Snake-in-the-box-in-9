# Independent verification of two complete induced paths

Both saved full-$Q_9$ positive vertex sets are complete induced paths with149 vertices and148 edges. This conclusion follows from direct checks of connectedness, recovered path order and all11026 unordered vertex pairs per witness. It does not depend on trusting the solver's positive status or an auxiliary-variable assignment.

| Probe under `data/full-probes/` | Exact counts along $012304$ | Total | Canonically oriented endpoints | Window start | Count indices |
| --- | --- | ---: | --- | ---: | --- |
| `012304-low-four-total22-full.json` | $(3,6,3,4,6)$ | 22 | $262\to133$ | 43 | 44,45,46,47,48 |
| `012304-low-four-total23-full.json` | $(4,6,4,3,6)$ | 23 | $262\to69$ | 113 | 114,115,116,117,118 |

Indices are zero based. In these orientations, the seven-vertex window is exactly $[0,1,3,7,15,14,30]$, with transition word $012304$. The data file records all149 vertices in this orientation, the148 transitions, and the alternative order starting at the numerically smaller endpoint. In that alternative order the windows are reversed and start at99 and29, respectively. The count tuples above always refer to the canonical window orientation; they are not reversed accidentally with the stored endpoint order.

For each set, the independent check established distinct vertices in $\{0,\ldots,511\}$, exactly two degree-one vertices, degree two at every remaining vertex, and one component. Starting at an endpoint and repeatedly taking the sole unused neighbour visits every selected vertex exactly once and ends at the other endpoint. For every pair of positions, the Hamming distance is one exactly when the positions are consecutive. Hence there are no chords. The five counts were recomputed by enumerating all21 eligible opposite corners at each internal window centre, and agree with the saved census and all bounds. Each record's source pins and probe script hash also match. All48 and94 saved cycle cuts, respectively, are valid induced cycles and are not fully selected.

The total22 path is an actual-snake counterexample to a universal $012304$ total lower bound23. It also satisfies the stated bounds $[(0,4),(6,21),(0,4),(0,4),(6,21)]$, so the same proposed lower bound fails on that restricted class. Both occurrences of6 are actual counts6. This statement is stronger than the earlier disconnected local-forest evidence. Neither witness matches every exact critical bucket tuple, and restrictions specific to those tuples require their own investigation. These148-edge constructions do not improve the known longest-snake lower bound and do not address optimality.

## Encoding inspection

`scripts/probe_full.py` uses `TaggedEncoding` from `milestones/10-window-aggregate/scripts/gen_lean_sat.py`, re-exported by `tagged_share.py`, with radius9 and the default endpoint budget2. Every vertex of $Q_9$ is then in the ball, and every vertex has all nine cube neighbours in that ball. The degree clauses force selected degrees at most two and at least one. The endpoint clauses force a flag at each selected degree-one vertex, forbid flags at degree-two vertices, and limit flags to two.

Thus every selected component is a nontrivial path or a cycle. The component census rejects a candidate containing any cycle component and adds its cycle cut before continuing. Once a positive acyclic selected graph is obtained, each component contributes exactly two endpoints. The endpoint budget and forced nonempty window imply that there is exactly one component. This explains why a positive acyclic full-cube result should be a complete induced path. The direct checks above independently establish the conclusion for both actual saved outputs.

The sum counter preserves all105 literal occurrences across the five corner lists, including any repeated vertices. Sorting does not remove repetitions. The count audit recomputes each centre separately and sums its count, thereby preserving the same multiplicities. No solver or Lean compiler was run in this review. No Lean statement is claimed here; any subsequent checked construction is separate evidence.

Pins:

- Total22 probe: `0e18001a791e9ba16eeb33304bd6f9f126d51982333d375d5e51dfa517338a76`.
- Total23 probe: `d9b13f9191a244622dfeba6006f7b8c1a1e42473eaa1dd4281b263c43ab97ec7`.
- `scripts/probe_full.py`: `acd1305dbf1431a7bbfea1d8810bba2d56de1556a73fc26925656dd138ef1c45`.
- `gen_lean_sat.py`: `33e6094ba48ddd8fa6cb7c9e9c2c2cab15c4e9a68908b0427125a2b11c683ecd`.
- `data/independent-full-witness-audit.json`: `9dd72b04fac6a860417de4afe85b17d58640cbd5b677044903837a5efd53e554`.
