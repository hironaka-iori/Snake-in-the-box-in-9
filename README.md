# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 230$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Contributor’s 230-edge audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/f5553b249ddf71f90e941f0641fb5a23366b3898/milestones/37-230-feasibility/audit230/final-audit.txt)

The short explanation compares 96- and 98-edge parents. The full paper gives the construction and the proofs. [Short explanation (PDF)](paper/pdf/snake9_frontier_explanation.pdf) · [Full paper (PDF)](paper/pdf/snake9_research.pdf) · [Manuscript sources and verification](paper/README.md)

## Latest result · Rounds 260–263

Suppose a nine-dimensional snake has at least 192 edges and crosses one coordinate exactly once. Any consecutive 96-edge segment in either face shares at most 44 of its 48 smaller-parity sites with the distant eight-dimensional reference in any placement. The previous bound for this reference was 46. The ceiling of 43 for the separate twelve-shape family still applies. [Distant-reference proof and scope](milestones/263-distant-family-certificates/README.md) · [Twelve-shape family](milestones/259-four-exchange-component/README.md)

The four rounds ruled out the remaining 21 shapes at exchange distances two and three from the distant reference. The construction search improved the attained lengths at 27 endpoints. Its longest verified join had 178 edges. [Donor intersections](milestones/260-donor-intersections/README.md) · [Rerouted partners](milestones/261-rerouted-partners/README.md) · [Common forbidden sites](milestones/262-common-forbidden-sites/README.md)

Paused after Round 263. [Active route](further-research/routes/ACTIVE.md) · [Long-term goal](further-research/routes/RESEARCH_GOAL.md) · [Other routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
