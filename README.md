# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 230$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Contributor’s 230-edge audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/ea5ecf3795d22d60d6578ecd26117049b5238e48/milestones/37-230-feasibility/audit230/final-audit.txt)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Rounds 258 and 259

Starting with six reference arms in the eight-dimensional cube, repeated exchanges of up to four smaller-parity sites reach exactly twelve 96-edge shapes. Their longest one-crossing join has 191 edges. A 192-edge join must avoid overlap on 44 or more of the 48 smaller-parity sites of any of these twelve, in every 96-edge window of either arm and every cube placement. [First four-site exchange](milestones/258-four-exchange-parents/README.md) · [Exact family maximum and attaining path](milestones/259-four-exchange-component/README.md)

Paused after Round 259. [Active route](further-research/routes/ACTIVE.md) · [Long-term goal](further-research/routes/RESEARCH_GOAL.md) · [Other routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
