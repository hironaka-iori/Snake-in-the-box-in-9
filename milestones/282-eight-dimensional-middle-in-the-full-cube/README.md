# Round 282. The 22 archived middle shapes anywhere in a nine-dimensional snake

**A 192-edge nine-dimensional snake cannot contain any of the 22 specified eight-dimensional paths as a consecutive interval.** Both free ends may grow in any of the nine coordinates, including returning to the face of the retained path. The same exclusion holds at every greater length by trimming free ends. Some archived 191-edge snakes contain these shapes, so the exact maximum across this family is **191**. The unrestricted nine-dimensional maximum remains open. [Per-shape bounds and proof coverage](coverage.json)

Round 278 required the path to cross one coordinate exactly twice and required the retained shape to be the entire path between those crossings. Round 282 requires only an occurrence of the shape. It may be a shorter part of a longer run in a face. The number and position of crossings are free.

## Why the extra crossings can be checked

Once a tail leaves the original face, it can return only to a vertex that is neither on the retained run nor adjacent to any vertex of that run. For the 22 original intervals, nine have no such vertices, six have one, and seven have two nonadjacent vertices. Consequently every return to the original face after leaving the run must be the last step of that tail. The lone available neighbour of the return site on the snake is its copy in the other face. Across the 22 intervals there are just 59 possibilities for the entire run in the original face and its additional terminal sites. [Argument and definitions](METHOD.md) · [All 59 possibilities](geometry.json)

For the 95-edge middle shared by 84 archived snakes of length 191, every site in the original face lies on the middle or touches it. That entire face is therefore unavailable for a return. There are three ways to finish the run in this face. All three have been covered. Any construction reaching 192 must change this 95-edge piece even if the old crossing points and both old arms are discarded.

## Verification

The original 22 paths are recorded in the same coordinates as Round 278. The full-cube calculation, the selection of paths in the opposite face and the final partitions by the neighbour of a crossing port all seek explicit paths. Complete contradictions have independently replayable LRAT proofs. The geometric audit also reconstructs the 59 patterns by enumerating subsets in the original face. The final upper bound uses only closed cases. [Full-cube results](full-192.json) · [Departures and returns](returns.json) · [Port neighbours](neighbours.json) · [Independent enumeration and replay](audit_middle.py)

The archive transfer checks occurrences up to cube isometry and reversal. The separate 191-edge searches and archived examples distinguish shapes where the individual maximum is known from those whose maximum may be 190 or 191. [Transfer to the two archives](archive-transfer.json) · [Individual length-191 searches](full-191.json) · [Computational receipts](runs)

At least one forbidden shape occurs in **98 of the 131 archived 191-edge snakes** and **549 of the 1,042 archived 190-edge snakes**. The counts of literal interval occurrences are 98 and 559. The individual full-cube maximum is 191 for three shapes and 190 for the 94-edge representative from `190-1`. For the other eighteen, 190 is attained and the ceiling is 191. Transferring the new exclusions improves the consecutive-overlap bounds for 36 further 191-edge records and 203 further 190-edge records relative to Round 281.
