# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 231$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Upper-bound proof revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088)

**Start with the [short explanation (PDF, 21 pages)](paper/pdf/snake9_frontier_explanation.pdf).** Page 18 compares the 96- and 98-edge parents. The [full paper (PDF, 240 pages)](paper/pdf/snake9_research.pdf) gives the classification and its proof on pages 154–155. [Manuscript sources and build records](paper/README.md)

## Latest result · Round 249

A 192-edge snake crossing once between two eight-dimensional faces needs a long parent outside the original fifteen recorded shapes. Of the eleven recorded 96-edge parents, five attain 191 and the six others give at most 190. The three recorded 97-edge parents give at most 190. The saved 98-edge parent gives between 179 and 187. The five shorter parents therefore account for every 191-edge join in the collection. [Argument and checked evidence](milestones/249-long-parent-joins/README.md) · [Five parents attaining 191](milestones/248-rooted-arm-capacity/README.md)

Research is paused after Round 249. Seven new long parents were found by changing one interior vertex. The next case is donor 16 at position 72. Any 95-edge partner at either end must visit the freed vertex 82. [Active route and ordered cases](further-research/routes/ACTIVE.md) · [Continuing goal](further-research/routes/RESEARCH_GOAL.md) · [Other research routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
