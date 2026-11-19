# Snake-in-the-box in nine dimensions

A snake is a path through a hypercube in which two vertices are neighbours exactly when they are consecutive on the path. Its length counts edges. The question is how long such a path can be in the nine-dimensional cube.

**The exact maximum is open. The reviewed bounds are $191 \le a(9) \le 231$.** The 191-edge witness contains 192 distinct vertices. The upper bound comes from a contributor's completed proof and saved audit. An independent rebuild of its full dependency chain is pending. [191-edge witness](outputs/snake9_witness.json) · [Upper-bound proof revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088)

**Start with the [short explanation (PDF, 20 pages)](paper/pdf/snake9_frontier_explanation.pdf).** The comparison between eight- and nine-dimensional snakes is on page 17. The [full paper (PDF, 238 pages)](paper/pdf/snake9_research.pdf) gives the arguments and their assumptions. [Manuscript sources and build records](paper/README.md)

## Latest result · Round 247

The displayed optimal 98-edge snake and five 96-edge snakes in dimension eight all have blocked endpoints. One of the 96-edge snakes accepts a partner of exactly 94 edges across a single crossing. Its longest join therefore has $96+1+94=191$ edges in dimension nine. For the displayed 98-edge snake, the partner can have at most 92 edges. [Eight-dimensional comparison](milestones/246-eight-dimensional-parents/README.md) · [Exact partner limit](milestones/247-relative-middle-placements/README.md#one-96-edge-parent-with-an-unrestricted-partner)

The five 96-edge snakes share a 47-edge middle. Fixing it leaves five longest disjoint partners of 48 edges each. All five were ruled out for a 192-edge join in the investigated crossing pattern. The nearest remaining 47-edge candidates each replace three vertices of the original partner. Research is paused after Round 247. [Round 247 results and certificates](milestones/247-relative-middle-placements/README.md)

## Explore the repository

| To find | Open |
|---|---|
| Recent results by research question | [Milestone guide](milestones/README.md) |
| A particular numbered round | [Complete round index](milestones/CATALOG.md) |
| The open cases at the pause | [Current research handoff](handoff/CURRENT_STATUS.md) |
| Witnesses, proof records and search programs | [Workspace map](WORKSPACE.md) |
| Earlier checkpoint reports and ledgers | [Historical documents](docs/history/README.md) |

The manuscripts are by Iori Hironaka, Tommy Ma and Steven Zhan.
