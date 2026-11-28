# Round 259 · An exact maximum for twelve one-crossing parent shapes

**The longest one-crossing join with any of the twelve parents has 191 edges.** The twelve comprise every 96-edge arm shape reachable from the original six by repeatedly replacing at most four of the 48 sites in its smaller parity class. The other 49 sites, the path order and both endpoints may change at every step. A join with arms of lengths 96 and 94 attains the maximum. Its 192 vertices passed all 18,336 pair comparisons. [Ordered 191-edge construction](attaining-191.json) · [Complete exchange graph](component.json)

## How the twelve shapes connect

With at most three replacements per step, the twelve split into three connected groups. A move between groups must replace exactly four sites. Each adjacent pair of groups has a single pair of shapes that permits such a move, up to cube isometry and path reversal.

| Group | Shapes | Connections to other groups at radius four |
|---|---:|---|
| Original references | 6 | Reference 0 to shape \(\mathtt{3e5b094f31a4}\) in the middle group |
| Middle group | 4 | The preceding connection, and \(\mathtt{c7b79d3cdf44}\) to \(\mathtt{479e57b7121a}\) |
| Last group | 2 | The preceding connection to the middle group |

Reaching the last group from the original six requires at least two steps of size four. There is a route attaining this minimum. From reference 0, replace four sites to reach \(\mathtt{3e5b094f31a4}\), one site to reach \(\mathtt{c7b79d3cdf44}\), and four sites to reach \(\mathtt{479e57b7121a}\). Each step has a labelled realisation, and cube isometries allow successive representatives of the same shape to be aligned. [First step](../258-four-exchange-parents/shell-0.json) · [Middle step](shell-3e5b094f31a4-1.json) · [Last step](shell-c7b79d3cdf44-4.json)

The six additional parents lie outside the earlier 264-shape catalogue. Their shells at distances zero through four cover 1,855,010,664,486 reference–candidate pairs. For every positive radius, a separate deletion-requirement enumeration recovered the ordered list of sets passing the physical-neighbour condition. Each such set was completed by two distinct path enumeration methods. At radius zero the spanning-order search allowed every completion of the fixed smaller class. Every successor of each of the twelve belonged to the twelve. The recorded transitions also connect them all, proving that the enumeration is complete for any number of steps. Lean separately checked the displacement bound for chains on the three groups. [Neighbour enumeration](neighbours.py) · [Independent supply enumeration](../258-four-exchange-parents/replay_supply.py) · [Graph reconciliation](component.py) · [Lean source](Bridges259.lean) · [Compiler receipt](Bridges259-compile.json)

## Why 192 is excluded

The original six arms already excluded a 95-edge partner at both ends. The six further shapes contribute twelve endpoint exclusions, all replayed from saved certificates. Any longer partner would contain a 95-edge prefix at the crossing. Thus a 96-edge parent in this family yields at most \(96+1+94=191\) edges in a one-crossing join. [Earlier six](../255-parity-exchange-arms/attainer-closure.json) · [First two new endpoint exclusions](../258-four-exchange-parents/partner-replay-95.json) · [Other ten endpoint exclusions](partner-replay-95.json)

Every 96-edge segment of either arm of a one-crossing snake of length at least 192 must share **at most 43 of its 48 smaller-class sites** with each of the twelve references, in every cube placement. Overlap of at least 44 would give a one-step exchange from a member, so the segment would be one of the twelve. Direct checks of both ends showed that none extends within its face. A proper segment of a longer arm would have such an extension. A whole 96-edge arm would require a partner of at least 95 edges. [Endpoint and overlap records](component.json)

**Global status.** The reviewed interval is \(191\leq a(9)\leq230\). Parents outside this component and snakes with multiple crossings remain open. The contributor’s saved audit passed at the pinned revision. A fresh independent rebuild of the full dependency chain remains pending. [Contributor theorem and audit](contributor.json) · [Manuscript receipts](manuscripts.json) · [Active construction route](../../further-research/routes/ACTIVE.md)
