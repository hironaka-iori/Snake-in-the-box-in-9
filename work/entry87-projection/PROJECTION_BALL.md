# How far must the projected address set move?

A 192-edge target has 193 vertices. Erase coordinate 5 from any of the 25 stored 191-edge snakes that cross this coordinate once. The source projects to a set W of 191 different eight-bit addresses. If a target omits d of these addresses and adds a new ones, it occupies 191−d+a addresses. Its number of doubled addresses, and hence its number of crossings along coordinate 5, is forced to be

    k = 193 − (191 − d + a) = 2 + d − a.

This identity lets us cover all choices of endpoints, order and layer assignments, including targets that change how often they cross the coordinate.

| Source addresses omitted | New addresses added | Required crossings | Labelled address choices per source |
|---:|---:|---:|---:|
| 0 | 0 | 2 | 1 |
| 0 | 1 | 1 | 65 |
| 1 | 0 | 3 | 191 |
| 1 | 1 | 2 | 12,415 |
| 1 | 2 | 1 | 397,280 |
| 2 | 0 | 4 | 18,145 |
| 2 | 1 | 3 | 1,179,425 |
| 3 | 0 | 5 | 1,143,135 |

These are all nontrivial cases with d+a at most three. Zero crossings would put the entire path in one eight-dimensional face, where the maximum is 99 vertices. A negative crossing count is impossible. Each row contains C(191,d) times C(65,a) indexed address changes before parity or degree filtering. Across the 25 sources the eight rows account for 68,766,425 indexed choices. Different sources may count the same target support.

**Result.** All eight rows fail for all 25 sources. Thus the projected address set of any 192-edge snake differs at four or more addresses from each of these labelled source sets. Across the 200 source and edit-count cases, 23 fail immediately by the number of possible doubled addresses. The other cases use 3,549 decisions partitioned by the least doubled address. All completed without needing a dynamic cycle clause.

## Exact decision

A doubled address already has one vertical edge at each of its two copies. It can have at most two occupied projected neighbours. In particular its number of neighbours in the original W is at most 2+d, since at most d of them can disappear. Enumerate the least doubled address among the candidates passing this bound. Two adjacent doubled addresses would form an induced square and are incompatible.

The two faces are selected jointly, with unrestricted occupancy subject to the prescribed edits and crossing count. Require full degrees one or two, exactly two endpoints, and connectivity. For odd k the endpoints are in opposite faces. For even k both are in one face and a global exchange puts them in face zero. For k=1 each of the two arms has at most 99 vertices, so in a 193-vertex snake the crossing is internal to the full path and has two occupied projected neighbours. For k greater than one the model permits an endpoint at a crossing. Disconnected cycle components can be excluded by their explicit vertices. Every path returned by the decision code is tested against every pair of nine-bit vertices.

The driver runs a positive control at every crossing count using a known 192-vertex path. The audit rebuilds the candidate-root list, checks the coverage of all eight edit sizes and all 25 source projections, checks the positive witnesses, and combines any required higher-budget retries by root. These are exact solver decisions. The separate unweighted bank classification has independently replayable resolution cores. [Decision code](single_hinge_exchange.py), [coverage audit](projection_ball.py), [complete combined outcomes](projection-ball-three.json).

The first balanced exchange outside this radius removes two addresses and adds two. There are 37,741,600 indexed choices per source. The target still has 191 projected addresses and must therefore cross twice. Its two endpoints lie in the same face, and its segment in the other face joins the two doubled addresses. Solving for both crossing addresses and every face assignment allows all three projected segments to move.
