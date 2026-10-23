# An asymmetric relation at Hamming distance four

Date: 24 October 2026. The integrated interval remains `191 <= a(9) <= 238`.

Let a snake contain the eight transition directions `(a,b,c,d,e,c,a,d)`, with five distinct coordinate labels, starting at position r. Write X and Y for its singleton counts at positions r+1 and r+7. These vertices have Hamming distance four.

Seventeen Lean dependency audits establish:

- X is at least 2.
- If X is at most 2, then Y is at least 4.
- If Y is at most 1, then X is at least 9.
- Consequently, X+Y is at least 5, 2X+Y is at least 8, and X+6Y is at least 15.
- If Y=1, the excess of X above its truncated value min(6,X) is at least 3. For distinct starts in one orientation, summing these excesses counts each charged position once.

No condition is imposed on the five intervening counts. The asymmetric conditions strictly strengthen the exact seven-count exclusion from milestone36. The initial four-position generalization, also checked here, is retained as an intermediate result.

## Evidence

| Forbidden upper bounds (X,Y) | Core clauses | Active variables | Certificate hints |
|---|---:|---:|---:|
| (1,21) | 14 | 13 | 23 |
| (2,3) | 1464 | 1066 | 73621 |
| (8,1) | 1152 | 966 | 23622 |

Every core is extracted from necessary radius-four conditions for an arbitrary snake. The clause interpretation, certificate replay, coordinate normalization, and final deductions are Lean-checked. The 17 dependency audits use only propext, Classical.choice, and Quot.sound. The positivity bridge reuses the mathematical identification from the existing aggregate development; it is rebuilt here without importing the unfinished direction-bound chain.

The first inequality also has a short geometric explanation. Relative to the first counted vertex, the opposite corners in coordinate pairs (c,d) and (d,e) are absent neighbors of already saturated internal segment vertices. They give two singleton squares. At the seventh counted vertex, pair (c,e) similarly gives one.

An independent census checks 17 positive local configurations among 36 probes. In particular:

| Pair (X,Y) | Selected vertices | Path components |
|---|---:|---:|
| (2,4) | 153 | 18 |
| (3,2) | 146 | 12 |
| (9,1) | 162 | 20 |

These forests attain the lower-boundary pairs in the radius-four model. Their degrees, interior endpoint budget, acyclicity, prescribed segment, and singleton counts are checked directly. No extension to a complete snake is asserted, and full-snake sharpness remains open.

## Effect on the active approach

The saved lower-table cycle from milestone36 contains one reversed occurrence of this shape, with pair (3,3). The saved witness-table cycle has no occurrence. Both satisfy the new inequalities. Their means, 119/29 and 29/6, therefore remain examples admitted by these added restrictions. This does not establish a global minimum mean or a new snake-length bound.

The excess rule gives a potential additional contribution of 72 per qualifying occurrence to the integer charge at scale12, before combining it with other charges. Reusing the same excess in another window requires a shared overlap budget. No universal frequency estimate has been proved.

## Reproduction

1. `scripts/probe.py` reproduces the bounded numerical tests. Solver exclusions remain numerical unless covered by the checked theorems.
2. `scripts/certify.py` generates the three numerical cores and Lean replay sources.
3. `scripts/replay.ps1 -Case 381`, then 382 and 383, checks the cores and refutations.
4. `scripts/check.ps1` rebuilds the positivity identification, initial four-position statement, arbitrary-coordinate pair inequalities, and excess accounting in a fresh output directory, using the existing Lean4.19/mathlib support libraries.
5. `scripts/archive.py --pack` or `--unpack` stores or restores the certificate files without loss.
6. `scripts/verify.py` checks core provenance, archives, proof receipts, all positive local witnesses, and the unchanged saved-cycle compatibility.

The exact maximum remains unresolved. The next useful target is a restriction that covers the surviving (3,3) window together with its intervening counts, or a broader family of shapes with a verified aggregate inequality.
