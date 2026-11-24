# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 230$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Contributor’s 230-edge audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/3e156b298f1a5ae9aa699965f5b76aff3e6b956e/milestones/37-230-feasibility/audit230/final-audit.txt)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Round 265

Of the 131 archived snakes of length 191, 25 cross a coordinate once. Even when both free tails are rebuilt, 191 is the exact maximum if the central 77 edges and the same single crossing are retained. The nine central segments up to symmetry give 56 completions of length 190 and 25 of length 191, all already in the published archives. [Enumeration and paths](milestones/265-joint-arm-regrowth/README.md)

The 398 archived one-crossing examples of lengths 190 and 191 also form a closed set under the specified simultaneous changes of one vertex and the free tip of each arm, as long as the join stays at or above 190. On a different 96-edge parent, direct regrowth improved the saved join from 132 to 182. [Exchange closure and independent verification](milestones/265-joint-arm-regrowth/summary.json) · [182-edge path](milestones/265-joint-arm-regrowth/best-open-join.json)

Paused after Round 265. [Active route](further-research/routes/ACTIVE.md) · [Long-term goal](further-research/routes/RESEARCH_GOAL.md) · [Other routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
