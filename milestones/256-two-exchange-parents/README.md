# Round 256 · Two simultaneous parity exchanges

Every 96-edge window inside either arm of a single-crossing snake of at least 192 edges must omit at least three of the 48 smaller-class vertices of **each of the six reference shapes**, under every cube isometry. Equivalently the overlap is at most 45. The six shapes comprise the five known parents attaining a 191-edge join and their sixth neighbour. The seventh, distant reference of Round 255 is outside this calculation. [Six reference identifiers and results](summary.json) · [Earlier partner ceilings](../255-parity-exchange-arms/README.md)

## Exact enumeration

For each labelled reference class \(U\), remove two of its 48 sites and add two of the other 80 sites of the same cube parity. Each resulting 48-set determines its removed and inserted pair uniquely. This gives \(\binom{48}{2}\binom{80}{2}=3{,}564{,}480\) candidates per reference. Counts across references retain multiplicities. Both endpoints, the traversal and all 49 opposite-class vertices are free.

| Reference (Round 248 class) | Candidates passing the neighbour count | Classes admitting an arm | Labelled arms | Shapes |
|---|---:|---:|---:|---:|
| 0 | 87 | 5 | 5 | 3 |
| 3 | 86 | 0 | 0 | 0 |
| 4 | 153 | 5 | 5 | 3 |
| 5 | 86 | 0 | 0 | 0 |
| 8 | 86 | 0 | 0 | 0 |
| Sixth reference | 121 | 5 | 5 | 3 |

In every positive row the three resulting shapes are the same, and all three already lie in the six-shape component. The complete new enumeration covers 21,386,880 reference and candidate pairs. [Enumeration](enumerate_shell.py) · [Independent edge selection](EnumerateExchanges.cs) · [Agreement on every labelled completion](replay.json)

## Why the exclusion is exhaustive

Each vertex of the smaller class is internal to a 96-edge path. It needs two distinct adjacent opposite-parity vertices. Each of those neighbours can have at most two neighbours in the selected class. After deletions, adding vertices can only increase those counts. Thus an insertion lacking two neighbours of current degree at most one can be discarded, and an existing class vertex lacking two neighbours of current degree at most two cannot be repaired by further insertions. A final class also needs two distinct opposite-parity endpoint labels of degree one. A count alone does not guarantee an arm.

For surviving sets, the first enumeration visits all spanning orders with legal endpoint attachments in the exact two-neighbour graph and expands all connector labels. The second independently changes direct integer neighbour counts and enumerates connected degree-two spanning subgraphs after adjoining the endpoint vertex. Both methods give identical labelled paths. All recorded completions passed the direct induced-path check. These finite classifications are native computations.

Round 255 closed the six shapes under moves of size zero or one. The exact size-two enumeration therefore proves closure under any sequence of moves of size at most two. Every member is reachable already by the former rule. The old capacity certificates give a maximum single-crossing join of 191 for this component. All 25 recorded attaining joins were reconstructed and each passed all 18,336 pair comparisons. All 96 possible endpoint extension slots in the six arms were checked again.

If a 96-edge window overlaps a reference on 46 or more smaller-class sites, its shape is in the component after alignment. If it is the entire arm, the partner ceiling applies. If it is a proper window, its containing arm would extend it by one edge, contrary to the endpoint checks. This proves the 45 bound for each of the six references. Other references and several-crossing constructions remain possible.

The global interval is \(191\le a(9)\le230\). The global witness was checked again. At contributor revision 9622e378, the saved audit reports 43,846 certificate interfaces and the three standard axioms. A full independent rebuild remains pending. [Contributor audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/9622e378d98a7b006f1abfdef67efcecbbbdbfcf/milestones/37-230-feasibility/audit230/final-audit.txt)

**Next decision.** Enumerate the exact three-exchange shell. Its completions are the closest possible candidates for a longer join on this route.
