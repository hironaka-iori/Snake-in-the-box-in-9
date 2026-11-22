# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 230$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Contributor’s 230-edge audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/062f86981cc6ee1e34577d6cbe600b3b057309c8/milestones/37-230-feasibility/audit230/final-audit.txt)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Rounds 256 and 257

Every 96-edge window in either arm of a single-crossing snake of at least 192 edges must replace at least four of the 48 smaller-parity sites of each of six reference arms, under every cube isometry. The six shapes remain closed under repeated exchanges of up to three vertices, and their maximum join is 191. From a seventh reference, three simultaneous exchanges can leave its previous component. [Two exchanges](milestones/256-two-exchange-parents/README.md) · [Three exchanges and partner constructions](milestones/257-three-exchange-parents/README.md)

Paused after Round 257. [Active route](further-research/routes/ACTIVE.md) · [Long-term goal](further-research/routes/RESEARCH_GOAL.md) · [Other routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
