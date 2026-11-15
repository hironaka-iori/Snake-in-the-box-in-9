# Endpoint coordinate parity: source preparation

Status: source prepared only; no compiler or native worker was launched. This optional module is independent of the repaired simultaneous constructor.

`EndpointParity225` imports the accepted `CutParity221` module. Its public `path_change_parity` repeats the existing private induction without changing the argument: the number of Boolean changes along the walk has residue zero for equal endpoints and one for unequal endpoints. The inductive step splits only the three relevant Boolean values.

`coordinate_crossing_count` applies that identity to the coordinate values of an arbitrary finite vertex walk and uses the natural-number quotient/remainder identity. Its conclusion is an actual nonnegative integer decomposition: crossing count equals endpoint disagreement plus twice a natural number. No path-validity or parity conclusion is assumed. Because the result applies to every vertex walk, it applies in particular to an actual induced replacement interval. The displayed walk includes an initial vertex, any middle vertices, and a final vertex, so this statement concerns intervals with at least one edge.

The module reuses the existing `changes` function and introduces no new definitions. The conversion from a concrete search model's coordinate-crossing variables to these actual changes remains a separate numerical/model obligation. No existence, exclusion, width result or new bound follows from this source alone.

Dependency: `milestones/221-square-parity/lean/CutParity221.lean`, accepted source SHA256 `24f789fd4c9f293925c190debe679ba4e535948c01bb664e061ac2a3cde37912`. The root should import its existing receipt/object before preparing this module. Two axiom reports are requested.
