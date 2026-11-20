# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 231$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Upper-bound proof revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Round 250

The seven new eight-dimensional parents obtained by changing individual interior vertices were checked at both endpoints. None of the 14 endpoints allows a single-crossing join reaching 191 in nine dimensions. Among all 22 reference shapes, exactly five reach 191. All five have 96 edges. The saved 98-edge parent can reach at least 179 and at most 187. [Round 250 evidence](milestones/250-corner-partners/README.md) · [98-edge parent](milestones/249-long-parent-joins/README.md) · [Five parents attaining 191](milestones/248-rooted-arm-capacity/README.md)

Regrowing both ends of the 134 distinct 84-edge segments from those references gives exactly 25 parent shapes of lengths 96–98. All six endpoints of the three additional 96-edge shapes exclude joins of 191 and 192. **Exactly five of the 25 shapes reach 191. A 192-edge single-crossing snake must avoid all 134 reference segments in every arm of length at least 96.** [Regrowth and endpoint evidence](milestones/250-corner-partners/README.md)

Research pauses after Round 250. On resumption, keep the same construction and use 80-edge reference segments to find parents outside the 84-edge catalogue. [Active route](further-research/routes/ACTIVE.md) · [Continuing goal](further-research/routes/RESEARCH_GOAL.md) · [Other research routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
