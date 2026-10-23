# Joint consistency of critical cycles

Research date: 23 October 2026. Two seven-centre exclusions have passed Lean, including arbitrary distinct coordinate labels. They remove the previously saved six-step witness-table cycle and 29-step lower-table cycle. The diagnostic search finds a replacement lower-table cycle at the same mean, so the integrated bound remains `191 <= a(9) <= 238`.

| Transition pattern | Seven internal singleton counts | Core clauses | Active variables | LRAT hints |
|---|---|---:|---:|---:|
| `(a,b,c,d,a,e,c,d)` | `(3,5,4,4,5,3,3)` | 1552 | 1155 | 67720 |
| `(a,b,c,d,e,c,a,d)` | `(2,5,4,5,3,5,2)` | 421 | 407 | 1023 |

In each row, a,b,c,d,e are distinct coordinates. Six transitive axiom audits passed with only propext, Classical.choice, and Quot.sound. The input clauses are necessary conditions on an arbitrary snake; the extracted cores and their refutations are checked separately. The first numerical core also uses short-cycle exclusions. No added lazy cycle cut was needed for either published certificate.

## Why these tests were selected

Neither saved critical cycle contains the pattern proved in milestone35. Strengthening that particular share bonus cannot remove either saved cycle. Instead, seven consecutive counts were required to hold on one common radius-four vertex configuration. Separate feasible five-centre windows need not have compatible overlaps.

All six phases of the witness-table cycle are solver-excluded. Among 29 phases of the lower-table cycle, 28 are solver-excluded and phase22 remains UNKNOWN after the bounded run. Only the two rows above have been upgraded to Lean theorems here. The other solver outcomes remain numerical evidence.

## Diagnostic graph

Two short prefix counters retain the information needed to detect the forbidden seven-count words. This adds 216 states, increasing the graph from 70416 to 70632 states. An independent comparison with complete seven-symbol histories checks all 279936 updates. Seven admitted edges are removed by the two new exclusions.

The saved witness-table cycle mean increases from 1739/360 to 29/6, an increase of 1/360. The saved lower-table mean remains 119/29 on a replacement cycle. These are exactly verified means of particular saved cycles. They do not certify a global minimum, the numerical share table, or a new bound on snake length.

## Reproduction

- `scripts/screen.py --table witness` and `--table lower` reproduce the bounded screens. Symbol6 means the interval6 through21; it is never fixed to6 in a lower-table test.
- `scripts/certify.py --case 3` and `--table lower --case 0` generate the two numerical cores and Lean replays.
- `scripts/replay.ps1 -Case 3`, then `-Case 100`, compile the replays in fresh directories.
- `scripts/check_extra.ps1 -Modules CriticalPattern,CriticalLower` checks the named-coordinate statements. These scripts use the existing pinned Lean4.19/mathlib support builds; they are incremental builds.
- `scripts/cycle_graph.py` reproduces the four saved graph diagnostics.
- `scripts/archive.py --pack` or `--unpack` stores or restores lossless certificate archives.
- `scripts/verify.py` checks input provenance, archives, source hashes, six axiom receipts, coarse-symbol interpretation, all history updates, and the saved cycle means.

The next useful target is a broader restriction covering related low-charge cycles, rather than merely increasing a weight on a pattern they avoid. The exact optimum remains unresolved.
