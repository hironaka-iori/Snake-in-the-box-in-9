# Independent mathematical review of the coupled model

The source correctly encodes a necessary degree relaxation of the stated restricted construction query, and its acceptance procedure requires an actual connected induced path. No unintended mathematical restriction or invalid cycle cut was found. The endpoint face and parity restrictions are consequences of the requested length, starting endpoint, and crossing count.

Read every line 1–128 of `scripts/coupled_search.py`, the saved forest-0 source record, the existing seed review, the current `joint-d4.json` result, and the execution wrapper. This was a mathematical source review. No optimizer, compiler, software tests, or new construction search were run; no model, native record, manuscript, or earlier review was modified. Only this log was written.

## Seed and coordinate interpretation

The source selects `bank_forests[index]` from `milestones/195-shortened-reroutings/data/forest-profiles.json`. For the current index 0, that record identifies bank entry 123 and original coordinate 7. Its lists are projected eight-bit vertices. Alternating the three complement components and two selected-face components, and adding 256 to the latter, makes coordinate bit 8 the crossing coordinate.

The recorded normalized seed has 192 distinct vertices, hence 191 edges, with endpoints 0 and 88. Its face occupancies are 94 lower and 98 upper. The five component edge lengths are $46,83,32,13,13$; they sum to 187, and the four crossings give 191. Crossing indices are 46, 130, 163, and 177. The source checks distinctness, the starting endpoint, and every unordered adjacency pair before constructing the model. The earlier seed review independently relates this normalization to the original bank extraction. This review inspected that source record and the saved seed statistics; it did not rerun the earlier bank-equivalence calculation.

The seed is used for omission constraints and a hint. Its 192 selected vertices do not satisfy the new 193-vertex target. A hint is not a selection constraint, so this discrepancy does not remove valid target assignments. No original component length, face occupancy, ordered port pairing, involution, or component exchange symmetry is imposed.

## Vertex count, induced degrees, and endpoints

There is a Boolean selection variable for every one of the 512 vertices of $Q_9$. The equation $\sum_v x_v=193$ specifies a prospective 192-edge path. The model does not confuse projected overlaps with repeated $Q_9$ vertices: the two layer copies are distinct variables and are counted separately.

For each vertex, the endpoint indicator satisfies $e_v\le x_v$. When $x_v=1$, the model requires

\[
\sum_{w\sim v}x_w=2-e_v.
\]

Thus all ambient cube neighbours selected with $v$ count toward its degree. No edge variable can omit an unwanted selected adjacency. Unselected vertices have no conditional degree restriction, which is correct: the degree under discussion is within the graph induced by the selected set.

The equations $e_0=1$ and $\sum_v e_v=2$ retain 0 as an endpoint and require one distinct additional endpoint. The second endpoint is otherwise free among vertices compatible with the necessary face and parity conditions. Specifically, a 192-edge path from the even vertex 0 ends at another even vertex. Exactly four changes of bit 8 put that endpoint in the same lower face as 0. Consequently setting all upper-face and odd-parity endpoint indicators to zero is valid. This leaves all 127 other even lower-face vertices available before the other constraints are applied. The old endpoint 88 has odd parity and cannot be the new final endpoint, but it may remain selected internally.

The selected parity equation requires 97 even vertices. Together with 193 total vertices, it gives 96 odd vertices, exactly the alternating parity counts of a 192-edge path beginning at 0. There is no requirement to preserve both old endpoints or the old endpoint pair.

## Four crossings and omission limits

For each projected vertex $v<256$, the three Boolean inequalities force

\[
c_v=x_vx_{v+256}.
\]

Therefore $\sum_v c_v=4$ counts exactly the selected bit-8 cube edges. In a connected induced path, each such edge must be a path edge, so the model imposes exactly four crossings. The four port labels and their traversal order are variable. The model does not fix the four original crossing locations.

For the 192-vertex seed set $S$, the omission expression is exactly

\[
\sum_{v\in S}(1-x_v)=|S\setminus T|,
\]

where $T$ is the target selected set. It is bounded above by the supplied `--omissions` argument. The additional constraints require at least one omitted original vertex in each normalized face. They impose the requested restriction on both faces; they are not necessary conditions for arbitrary 192-edge snakes.

If $d$ seed vertices are omitted, then $193=(192-d)+|T\setminus S|$, so exactly $d+1$ new vertices are added. For the saved `--omissions 4` run, the two per-face lower bounds imply $2\le d\le4$, with three through five additions. Retaining root 0 is an additional explicit restriction and must remain in any reported exclusion scope.

Requiring an omission in both faces does not require a crossing port to change. All four original ports may remain selected. This is consistent with the task's requirement that all ports be variable. It differs from the optional seed-review suggestion to force replacement of at least one port; that extra restriction is absent. The seed review also suggested an initial budget of 12, whereas the saved run explicitly uses 4. Neither difference is a model error, but neither optional condition should be attributed to this run.

## Square cuts, disconnected components, and acceptance

The square loop includes each coordinate square once, using its smallest vertex as representative. There are $\binom{9}{2}2^7=4608$ such squares, matching the saved record. The cut $\sum_{v\in C}x_v\le3$ is valid because an induced path cannot select all four vertices of a square.

The degree model alone does not impose connectedness. With exactly two degree-one vertices and all other selected degrees equal to two, every feasible selected graph consists of one path containing both endpoints and possibly additional cycle components. The endpoints cannot lie in different components: each finite component has an even number of odd-degree vertices. Isolated selected vertices are excluded by the degree equations.

The source reconstructs all selected adjacencies and connected components after each native feasible result. A connected component whose vertices all have degree two is a cycle. Requiring at least one vertex of each such cycle to be omitted is valid for every induced path, including paths that would use that region in another way: selecting the entire cycle would preserve all its internal cube adjacencies. These cuts do not fix a cycle's external attachment or exclude a valid induced path.

If there are no cycle components, the source requires one connected component, traces it from 0, verifies 193 distinct vertices, and checks every unordered vertex pair against the consecutive-index condition before reporting `WITNESS`. This prevents a disconnected degree solution from being reported as a construction. The source uses the model for the omission and crossing constraints; its final explicit pair check verifies inducedness and length, rather than independently rechecking every model restriction. A future witness should retain a separate full saved-witness audit before stronger publication claims.

The exported `.pbtxt` is the initial model. If dynamic cuts are subsequently added, they are recorded in the result's `cycle_cuts` list, but the script does not re-export a final model. This is a provenance limit, not an invalid mathematical cut. Any later replay of a post-cut exclusion must combine the initial model with the recorded cuts. The currently inspected d4 result has no dynamic cuts, so that distinction does not affect this particular result.

## Permissible interpretation of outcomes

The currently saved d4 record reports `INFEASIBLE` in its first native iteration, with no witness and no dynamic cycle cuts. This review has not independently checked the native solver's infeasibility derivation or reconstructed the serialized model. It supplies a validity review of the encoding, not a new exact or Lean exclusion certificate.

Assuming the saved native result and model correspondence are accepted, the exclusion concerns only index-0 seed alignment, root 0 retained as an endpoint, exactly 193 vertices, exactly four bit-8 crossings, at most four seed omissions, and at least one omission in each face. A larger omission budget, a changed root, a different seed alignment, a different number or coordinate of crossings, or a change confined to one face is outside that statement. No translation or symmetry argument has been supplied to remove the retained-root or fixed-seed restriction.

For any future run, `UNKNOWN`, `TIME_LIMIT`, or a resource interruption establishes no exclusion. A native `INFEASIBLE` result for a model with the valid accumulated cuts still concerns only the explicit query restrictions. Nothing here establishes a global upper bound, classifies all coupled reroutings, or supplies a construction above 191.

## Inspected hashes

| File | SHA-256 |
|---|---|
| `scripts/coupled_search.py` | `ad4328aeca4b8b61ad02dcae0a078075eb5c84a3611ddf193c84a3aa63ecf068` |
| `195-shortened-reroutings/data/forest-profiles.json` | `9a29adaef98c59a9e6c7d28e633af8bc010defbbda0831aa456a61d46b0a929f` |
| `data/joint-d4.json` | `3df4967aaf726c4db222d577f13507b227425c82a57607a46354905cd2f91932` |

The source hashes in the saved result agree with the inspected script and profile file. No model edit is requested by this mathematical review.
