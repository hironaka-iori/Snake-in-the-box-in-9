# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 231$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Upper-bound proof revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088)

**Start with the [short explanation (PDF, 21 pages)](paper/pdf/snake9_frontier_explanation.pdf).** Page 18 compares the 96- and 98-edge parents. The [full paper (PDF, 239 pages)](paper/pdf/snake9_research.pdf) gives the classification and its proof on pages 153–154. [Manuscript sources and build records](paper/README.md)

## Latest result · Round 248

For each of five recorded 96-edge snakes in dimension eight, the longest possible partner across one crossing has exactly 94 edges. Only one endpoint of each parent attains this maximum. At that endpoint exactly five labelled partners attain it, accounting for all 25 published joins in the family. Thus the exact maximum for these parents is $96+1+94=191$. The displayed 98-edge parent accepts at most 92 partner edges. [Classification and proof records](milestones/248-rooted-arm-capacity/README.md) · [Eight-dimensional comparison](milestones/246-eight-dimensional-parents/README.md)

Research is paused after Round 248. The marked route continues with the six other recorded 96-edge parent shapes. [Active route and resumption point](further-research/routes/ACTIVE.md) · [Other research routes](further-research/routes/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
