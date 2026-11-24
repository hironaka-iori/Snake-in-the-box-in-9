# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 230$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Contributor’s 230-edge audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/3e156b298f1a5ae9aa699965f5b76aff3e6b956e/milestones/37-230-feasibility/audit230/final-audit.txt)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Round 264

All 41 eight-dimensional arm shapes reachable from the distant reference by repeated exchanges of one smaller-parity site exclude a 192-edge one-crossing join. This covers all 82 endpoints and every 96-edge segment inside a longer arm. A join of length 181 is known in the family. Its maximum is at most 191. [Proof, witness and endpoint coverage](milestones/264-distant-component/README.md)

A 192-edge snake can also be specified by choosing and ordering the 96 vertices of its smaller parity class. Each consecutive pair needs a connector with exactly those two neighbours in the class, and each end needs a neighbour attached only there. The paper applies this description to reconstruct and count opposite arms. [Parity construction and counts](milestones/264-distant-component/README.md#turning-the-192-edge-question-into-a-graph-on-one-parity-class) · [Earlier distant-reference bound](milestones/263-distant-family-certificates/README.md)

Paused after Round 264. [Active route](further-research/routes/ACTIVE.md) · [Long-term goal](further-research/routes/RESEARCH_GOAL.md) · [Other routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
