# Round 241. Exact neighbour-count distance

The smallest possible number of count changes between distinct binary selections of \(Q_9\) is eight. Seven arbitrary erasures are recoverable. The eight-count change is unique up to cube isometry and overall sign, and it replaces twenty vertices by twenty others on one parity side. For the saved bank, any hypothetical 192-edge snake must change at least eighteen labelled counts relative to each seed.

| Evidence | Scope |
|---|---|
| [Written proof](MATHEMATICAL_NOTE.md) | Universal seven-erasure recovery, two explicit selections attaining eight, and the saved-seed consequence with its finite premises. Includes two lower-bound arguments. |
| [Equality classification](EQUALITY_CASES.md) | Written reduction to six block patterns, exact exterior calculations and an independent written derivation of the surviving character. |
| [Direct count](witness.json) | Both explicit selections and their eight signed discrepancies. The verifier independently counts distance-one neighbours at all 512 positions. |
| [Native character calculations](four-block-certificate.json) | All 48 exterior maxima for the six patterns. |
| [Actual-cube Lean statement](lean/EightCountWitness241.lean) and [compiler receipt](EightCountWitness241-compile.json) | Ternarity, all nine-flip sums at every vertex, the exact signed profile, eight distinct positions and a positive selected difference. The universal lower bound and equality classification remain outside this module. |
| [Research manuscript receipt](snake9_research-compile.json) and [short explanation receipt](snake9_frontier_explanation-compile.json) | Compiled the authoritative documents and checked their repository mirrors. The new sections begin on PDF pages 145 and 15, respectively. |

The first attempt to check all 512 points in one Lean decision exceeded the 256 MiB process limit. Splitting the proof into 32 groups of 16 vertices produced the accepted module within the same limit. The successful check used one Lean thread and the 60-second module deadline. A Windows job applied the 256 MiB hard limit to each compiler, with the 1 GiB startup gate and 768 MiB reserve.

## Construction and contributor status

Round 240 was published at [cdc9efe9](https://github.com/hironaka-iori/Snake-in-the-box-in-9/commit/cdc9efe96c837f28b9c0d6b305320218444e8b5b). This round started from the subsequent [published handoff](https://github.com/hironaka-iori/Snake-in-the-box-in-9/commit/80784a6d0dd638ef114a5fe158110e63841dada3). The construction searches frozen at Round 240 retain their saved outcomes. The 18-count consequence uses the existing majority-extension and minority-preservation exclusions for the 131 saved seeds. No 192-edge witness was obtained, and the conjectured length 196 remains open.

The reviewed interval is \(191\le a(9)\le231\). The completed 231 theorem and saved audit are pinned to contributor revision [478869ee](https://github.com/hironaka-iori/Snake-in-the-box-in-9/commit/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088). The [subsequent contributor report](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/2ecb7a57688b9935a403d4bee456874e369cf364/milestones/38-220-conditional/README.md) gives 229 conditional on the stated certificates. The [sample rebuild](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/2ecb7a57688b9935a403d4bee456874e369cf364/milestones/36-lean435-port/audit231/sample-rebuild/README.md) covers 275 of 24,797 certificates. A fresh independent rebuild of the full dependency chain remains pending.

## Related literature

The support inequality is a sign-cube instance of the distance of an affine Cartesian evaluation code. The signed two-coordinate factor also occurs in work on minimum-support functions on Hamming graphs. The earlier literature on detecting families treats the choice of counting queries, while Smith-group calculations address integral matrix equivalence and spherical bitrades impose their own local count conditions. These results have different hypotheses from the exact count distance proved here. No priority claim is made. [López, Rentería-Márquez and Villarreal, Theorem 3.8](https://arxiv.org/pdf/1202.0085#page=10) · [Valyuzhenich and Vorob’ev, Section 3](https://arxiv.org/pdf/1807.09139#page=3) · [Lindström](https://real.mtak.hu/189070/) · [Chandler, Sin and Xiang](https://arxiv.org/abs/1511.00272) · [Mogilnykh and Solov’eva](https://arxiv.org/abs/1912.09089)

## Next decision

Pause after publication for review of the counterexample to the minimum-nine conjecture. On resumption, compare the classified eight-count minority changes with the membership signs of the saved seeds. Move the seed and the change together under a cube isometry, or use only the fixed seed's stabilizer. A surviving sign pattern would still require a compatible majority change and a verified 193-vertex induced path. A complete seed-specific exclusion would concern only this boundary family. The next scheduled full written-source review is Round 250.
