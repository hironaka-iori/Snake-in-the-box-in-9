# Round 264 · A parity construction and the 41-shape one-crossing family

A 192-edge one-crossing snake cannot contain any of the 41 shapes reachable from the distant 96-edge reference by repeated changes of one smaller-parity site. This holds for a whole arm and for any 96-edge interval of a longer arm. The longest possible join for this family lies between 181 and 191 edges. The 181-edge construction was rechecked against all 16,471 pairs of its vertices. [Coverage and ordered witness](summary.json) · [Earlier component enumeration and independent replay](../255-parity-exchange-arms/closure-replay.json)

## Turning the 192-edge question into a graph on one parity class

A 192-edge snake in the nine-cube has 96 vertices of its smaller parity class. Choose a set \(S\) of 96 vertices of one parity. Join \(u,v\in S\) in a new graph if some opposite-parity cube vertex has precisely \(u,v\) as its neighbours in \(S\). Mark a vertex \(u\in S\) if some opposite-parity cube vertex has \(u\) as its only neighbour in \(S\). Then \(S\) is the smaller class of a 192-edge snake if and only if this graph has a path visiting all 96 vertices exactly once and both ends are marked. Earlier rounds established the parity contraction. Here the order is used to count and construct its expansions under additional forbidden sites. [Earlier parity construction](../../paper/snake9_frontier_explanation.tex)

For an order \(x_1,\ldots,x_{96}\), write \(c_i\) for the number of available labels with neighbours \(\{x_i,x_{i+1}\}\). Write \(t_1,t_{96}\) for the available labels with sole neighbour \(x_1,x_{96}\), respectively. The number of oriented expansions is \(t_1t_{96}\prod_{i=1}^{95} c_i\). Each label has exactly the neighbours required by its position. Different positions have different neighbour sets and therefore cannot reuse a label. The cube has no edges within either parity. These facts give both directions of the construction and justify multiplying the counts.

In the three-cube the ordered pair \(000,110\) illustrates the rule. Its two connectors are \(010,100\), and its endpoint labels are \(001,111\). There are exactly two oriented expansions. In the unrestricted nine-cube the choice of \(S\) and a spanning order remain open.

## An application with the crossing fixed

Translate the joining vertex to zero in each eight-dimensional face. The opposite arm starts at their common vertex zero and must avoid every other projected parent site. For a 95-edge partner the even side has 48 sites including zero. Its 47 consecutive pairs need connectors, and only the last even site needs an endpoint label. Each factor counts the choices after deleting the other projected parent sites.

The construction compares donor prefixes with the same ordered even sites. The rigid comparison retains the whole prefix. In the parity construction all intermediate odd vertices, and the final odd vertex when present, can vary. Every coordinate permutation was considered. The reported maxima refer to these donor prefixes.

| Comparison at the twelve ends of the six outstanding shapes | Result |
|---|---|
| 1,008 normalised rooted donor words of length 95 | Six endpoints improve. The largest gain in partner length is 28 to 35. The largest partner in this collection has 39 edges. |
| Full 48-site even class of the same donors, with arbitrary order and odd sites | At least three donor even sites must change at every endpoint. The minimum is three at five endpoints, four at three, and five at four. |
| 5,570 rooted words after adding directed suffixes of earlier constructed partners | The largest join has 175 edges. At each endpoint both construction rules attain the same maximum length. |

The first calculation intersects the allowable coordinate permutations at each site and takes their union over possible connector labels. A separate enumeration reconstructs every longest ordered even class in the physical coordinates, counts the expansions, and rules out the next length. Every saved join passes all-pairs verification. The minimum number of forbidden even sites was calculated by binary addition of intersection indicators and by a separate prefix count. [Parity construction](repair.py) · [Original donor results](constructions.json) · [Expanded donor results](expanded-constructions.json) · [Independent counts and coverage](audit.py)

## Exclusion for an unrestricted partner

A 96-edge arm would need a 95-edge opposite arm to reach 192. A longer partner can be shortened at its free end. Normalised forbidden sets from earlier proofs cover 72 of the 82 endpoints by explicit coordinate permutations. At the ten remaining endpoints, seven have a contradiction for the whole root and three have certificates for all seven possible first edges. The 28 new contradiction certificates were checked against their regenerated Boolean formulas. Every qualifying 95-edge induced path satisfies the encoded constraints. One time-limited whole-root computation was subsequently resolved by its seven first-edge cases. [Root data and source pins](endpoints.json) · [Proof archive](proofs/) · [Solver and replay](endpoints.py)

All \(41\cdot2\cdot8=656\) possible one-edge extensions in the parent face fail. Thus a 96-edge window inside a longer arm cannot be one of the 41 shapes. If the window shared at least 47 of its 48 smaller-parity vertices with any member under a cube isometry, one allowed exchange would place the window in the same closed component. The resulting ceiling is 46 common sites for every member. The previously proved ceiling of 44 for the starting reference is stronger. [Extension and root coverage](summary.json) · [Starting-reference ceiling](../263-distant-family-certificates/README.md)

The global interval is \(191\leq a(9)\leq230\). The 191-edge control was reconstructed from its two arms and all 18,336 vertex pairs were checked. The contributor's 230-edge upper bound has a saved interface audit. A fresh independent rebuild of the full dependency chain remains pending. [191-edge control](../259-four-exchange-component/attaining-191.json) · [Contributor theorem and audit](contributor.json) · [Manuscript verification](manuscripts.json)
