# Superseded interruption

The user resumed work on 18 November 2026 through round 239. Round 237 now has completed replay receipts and compiled manuscripts; this earlier pause record is retained as history. Continue through 239.

# Round 237 paused unfinished

Paused at the user's request on 18 November 2026. Round 236 at commit `75b2f41e` is the last published construction round. Round 237 is an uncommitted working checkpoint. The reviewed contributor theorem gives the global interval from 191 to 231 edges. Optimality remains open.

## Results available locally

- Two independent enumerations of the 177,062,400 majority exchange descriptions returned the same 679 survivors, representing 623 distinct 97-vertex sets. One seed majority vertex was removed and two were inserted. Independent native necessary-degree and circuit models exclude the family. See [the reconstruction record](degree/independent-results.json) and [source review](degree/independent-review.md).
- Together with the prior minority exclusions, the computational evidence bounds overlap with each saved 191-edge seed or cube-isometric copy by 186 vertices. A 192-edge candidate would need at least six deletions and seven additions. This is a restriction relative to the seed bank.
- The full cube inverse and recovery of a binary selection from the neighbour counts at any 510 of the 512 vertices passed Lean. See [the proof](parity/CubeInverse.lean) and [compiler output](parity/compiler.log).
- The path-degree and directed-cut lemmas have compiler records in [spectral](spectral/README.md). The final bridge from the numerical contraction counts to the path-index theorem was still under review.

## Interrupted verification and manuscript

The 623 explicit numerical cut witnesses are in [cuts.json](majority/cuts.json). During the serial Lean replay, the runner reported successful modules from `Cuts000` through `Cuts275`, 25 statements each. This covers indices 0 through 299. The user requested a stop before a complete audit. The runner was stopped and produced no final `kernel-cuts.json`. The first outstanding index is 300. The existing checker can rerun the complete batch to create the final receipt after resumption. Full enumeration coverage and the mapping of the saved bank to the cut inputs are separately supported by the independent computational reconstruction.

The [provisional manuscript passage](../../work/round237/round-section.txt) has not been integrated into either maintained manuscript. Some draft sentences anticipate a complete kernel audit. Use the observed run status above until a final receipt exists. The maintained manuscripts still display round 236. The contributor's published [231-edge theorem and audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088/milestones/36-lean435-port/audit231) should be incorporated on resumption. Round 237 manuscript compilation and GitHub publication remain pending.
