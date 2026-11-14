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

Extract the [207 original runs](projection-ball-inputs.zip) in this directory before running `python projection_ball.py`.

The first balanced exchange outside this radius removes two addresses and adds two. There are 37,741,600 indexed choices per source. The target still has 191 projected addresses and must therefore cross twice. Its two endpoints lie in the same face, and its segment in the other face joins the two doubled addresses. Solving for both crossing addresses and every face assignment allows all three projected segments to move.

## The middle arm must have 65 through 99 vertices

**Lemma.** An induced linear forest (a disjoint union of paths, including isolated vertices) in a four-cube has at most eight vertices. A parity class attains eight.

First consider a three-cube. Six selected vertices already induce at least six edges, since deleting two vertices from the twelve-edge cube removes at most six edges. Five vertices in a linear forest must form a single path. Indeed, if their three omitted vertices span h edges, the selected set spans 3+h edges. If h is positive, the forest property forces h=1 and yields a connected path. If h=0, the omitted triple has one parity: any opposite-parity independent pair in the three-cube is antipodal, and its two neighbourhoods cover all other vertices. The fourth vertex of that parity then has three selected neighbours, which contradicts the degree bound.

Suppose nine vertices in a four-cube induce a linear forest. Splitting into two three-cubes gives five on one side and four on the other. The five form a four-edge induced path. Up to symmetry its transition word is 0120: repeating a bit immediately revisits a vertex, and three consecutive steps of the form i,j,i create a chord. Its vertices are therefore 0,1,3,7,6. In the other face the copies of 1,3,7 are forbidden, since each would give a middle vertex degree three. Four addresses must be chosen from 0,2,4,5,6. If both 0 and 6 are chosen, at least one of 2,4 joins them in that face, closing a cycle through the original path. If one endpoint is omitted, the other is chosen together with 2 and 4. It has two horizontal neighbours and its vertical neighbour, hence degree three. This proves the lemma.

A Q8 face partitions into sixteen disjoint four-cubes. The portion of any induced snake in that face is a linear forest and hence has at most 128 vertices. With exactly two crossings, the opposite face contains one middle arm. A 193-vertex full path therefore puts at least 193−128=65 and at most 99 vertices in this arm. Its size minus one has the same parity as the Hamming distance between the two crossing addresses.

The upper endpoint uses the known eight-cube maximum of 98 edges. [Östergård and Pettersson, Exhaustive Search for Snake-in-the-Box Codes](https://research.aalto.fi/en/publications/exhaustive-search-for-snake-in-the-box-codes/).

**A crossing-pair exclusion.** No occupied projected vertex can be adjacent to both doubled addresses. In its own face it must join one copy of each doubled address. Those two edges, together with the two crossing edges, force the three-vertex segment between the crossings. This contradicts the lower bound of 65. In particular, if two proposed crossings are at distance two, both common neighbours of their addresses must be absent. At edit distance four, any of those common neighbours present in the source must consume one of the two deletions. The search now uses this implication before it assigns the two outer arms.

For the balanced two-for-two exchange, count the possibilities for the two crossing addresses before constructing a path. The sieve checks base degree one or two at both addresses, independence, the absence of a shared occupied neighbour and the bipartition sizes of the new support. It leaves **1,464 indexed crossing pairs** across 25 sources, or 45 to 73 pairs per source. The pair and address-set counts agree with a second program that explicitly visits all 943,540,000 indexed exchanges across the 25 sources. [Grouped count](crossing_pair_filter.py), [all surviving pairs](crossing-pair-filter.json), [literal checker](crossing_pair_control.cpp), [independent counts](crossing-pair-control.json).

## Searching beyond the original address sets

The separate two-crossing bank has 88 sources, of which 84 share one 95-edge middle. All three middle shapes represented there are already excluded at 192 edges. [Classification of the 88 sources](DOUBLE_CROSSINGS.md).

The completed 97-vertex Q8 regrowth menu contains 51 inequivalent paths. Five already have checked two-crossing exclusions. This leaves 46 specified middles for unrestricted two-arm completion. Fix a middle in one face and place the two copies of its endpoints in the other face. Use another 94 vertices of that other face to form two mutually nonadjacent outer arms containing 96 vertices in all, with one crossing root in each. Both roots have the same base parity. A 48,97,48 split is one permitted profile; the decision searches all splits. Every positive result is reconstructed and every pair of its 193 vertices is checked. [The 46 paths](regrown-middles-menu.json), [experiment](regrown_middles.py), [two-arm solver](bank_two_arms.py).
