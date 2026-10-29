# Milestone 66: complete-model integration and manuscript revision

**Completed research round and manuscript revision.** The existing paper integrates rounds 57–66 and compiles successfully in the desktop editor. The new local count proofs and arithmetic passed 3 Lean modules and 16 theorem audits. All previous mathematical statements and witnesses are preserved; the paper has 116 statements and 164 labels. The global optimum remains unresolved, and no new universal upper bound is claimed.

## Complete-model effect

The milestone-65 terminal-count restriction has been integrated into the complete recorded nine-transition model using additional direction history. Its exact integer minimum rises from 9891/20 to **18823/38**, an increase of **301/380**. The normalized mean is **18823/4560**.

The construction tracks prefixes of the three successive canonical nine-direction windows forming the relevant eleven-direction pattern. Enumeration of all **11,162** canonical induced eleven-direction words verifies that the three-window signature identifies that pattern uniquely. It adds 15,552 states, rather than retaining every eleven-direction word in every state. This recognition has an exhaustive computational check; its arbitrary-snake proof bridge remains unfinished.

An independent verifier reconstructs every lifted transition and checks every integer potential inequality and an attaining cycle. The potential range is 23,459 at denominator 38. The inherited boundary accounting gives the conditional estimate

\[
m\le\frac{41\,961\,883}{178\,423},
\]

whose integer consequence remains 235. The source model still contains inherited numerical premises and lacks a complete checked graph-to-snake assembly. These finite computations do not establish a new global bound.

## Shares and recognition limitation

Eight of the nine count-conditioned share improvements from milestone 65, together with the earlier geometric bounds for those patterns, can use the same prefix construction. They strengthen **175,293 lifted transitions**, but leave the minimum unchanged. Shares on the same centres are combined by their maximum.

The remaining pattern, transition 115, has an ambiguous signature. Both direction words

\[
(0,1,2,3,4,2,1,5,6,3,0),\qquad
(0,1,2,3,4,2,1,5,6,3,7)
\]

have the same three canonical nine-window labels. The first word has a checked share inequality; that theorem supplies no inequality for the second word. Consequently this rule is omitted from the lifted model. Additional coordinate memory, or a separate proof covering the second word, is needed to recover it.

## Two further direct count restrictions

All named coordinates in each of the following words are distinct. Two new arbitrary-snake theorems have passed Lean, with **two modules and ten standard-axiom dependency audits**:

| Eleven directions | Internal position | Singleton lower bound |
|---|---:|---:|
| (a,b,c,d,e,f,d,c,a,b,d) | 8 | 3 |
| (a,b,c,d,e,f,d,c,a,f,d) | 10 | 3 |

Each proof exhibits three opposite corners forced absent by selected vertices that already have their two path neighbours. With the coordinates normalized to 0 through 5, the first proof uses vertex 51 and corners 17, 27, 33; the second uses vertex 18 and corners 6, 17, 23. No count assumptions at other positions are required. The finite corner witnesses were independently reconstructed.

These restrictions exclude two windows of the first replacement cycle. Integrating them excludes 17,161 lifted transitions in total, including the original terminal restriction. Another minimum-mean cycle survives, so the mean stays 18823/38.

## Model comparison

| Model | States | Transitions | Exact integer mean |
|---|---:|---:|---:|
| Inherited nine-transition model | 1,026,432 | 11,594,078 | 9891/20 |
| Original terminal restriction | 1,041,984 | 11,772,559 | 18823/38 |
| Original restriction and eight share patterns | 1,143,072 | 12,893,079 | 18823/38 |
| Above plus two new count restrictions | 1,166,400 | 13,173,896 | 18823/38 |

The extra transitions arise from storing necessary history. Every lifted transition projects to an inherited transition; removing particular lifted transitions is meaningful within each lifted state space, rather than as a comparison of raw edge totals between different graphs.

## Complete remaining critical family

All edge slacks are nonnegative under the exact potential. A minimum-mean cycle has total slack zero, so each of its edges is tight. Extracting the strongly connected components of the tight-edge graph identifies **all 70 critical states and 99 critical transitions**, in one component. The data are in `data/critical-family.json` and `data/critical-edges.json`.

The next research round should compute certified empty-square shares over this entire family. Checking only one displayed cycle can miss other cycles attaining the same mean, as the two new exclusions demonstrate. This remains the empty-square charging route; the direct count restrictions enforce the geometry of the configurations being charged.

## Evidence and remaining tasks

- `data/model-verification.json`: independent reconstruction and exact potential checks for the first two lifted models.
- `data/pressured-verification.json`: independent check of all 13,173,896 transitions of the final model.
- `data/count-lean-audit.json`: both new arbitrary-snake count theorems, source hashes and ten dependency checks.
- `data/new-count-certificates.json`: three-corner witnesses for both proofs.
- `data/replacement-cycle-probe.json`: candidate share gains on the earlier replacement cycle; these candidates have not been added as new share rules.
- `scripts/lift_terminal.py` and `scripts/lift_shares.py`: complete-model construction, with source hashes and explicit ambiguous-pattern handling.
- `scripts/analyze_terminal.py`: exact potential and attaining-cycle check, accepting `terminal`, `shares` or `pressured`.
- `scripts/verify_models.py`: independent reconstruction; pass `pressured` to verify the final model separately.
- `scripts/critical_family.py`: complete tight cyclic-component extraction.
- `scripts/replay.py`: the two new Lean modules, using the completed milestone-65 dependency build.

The manuscript rewrite is complete. Its source and existing editor mirror are identical, with the three authors and hyperlink settings preserved. The source audit verifies all 108 prior statements, eight additions and all thirteen printed snakes (118,673 pair checks). The desktop editor compiler succeeded after one stale-project response. Rendered pages have not been visually inspected, and no replacement PDF was generated. The current source hash is `d422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341`. See `data/paper-verification.json`, `data/editor-compile.json`, `data/lean-audit.json` and `data/repository-check.json`.

This completes the ten-round cycle after manuscript revision 56. The next scheduled full rewrite is milestone 76. The next mathematical task is to strengthen shares over the complete remaining critical family, including alternatives to a single displayed cycle.
