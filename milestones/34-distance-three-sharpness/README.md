# Sharpness of the distance-three inequalities

Research date: 23 October 2026. Both constants from milestone33 are attained by complete snakes and cannot be increased universally. The optimum snake length remains unresolved.

| Pattern | Witness edges | Window start index | Pair counts | Sum |
|---|---:|---:|---|---:|
| 0123410 | 143 | 67 | 6,4 | 10 |
| 0123415 | 138 | 70 | 5,4 | 9 |

The vertices are indexed from zero. Initial vertices are 193 and 77, respectively. The paper includes complete transition sequences; `data/witness-*.json` contains ordered vertex lists and provenance.

## Evidence

Twelve Lean audits check distinctness, every pair's adjacency, the seven directions, both singleton counts, attainment, and impossibility of increasing either universal constant. All audits use only propext and Quot.sound. These are complete induced paths, rather than local forests. The proofs use the repository's existing Snake definition and coreAlpha counts.

The initial radius-four tests also attained 10 and 9, but had 18 and 19 components. A separate full-cube model, followed by explicit cycle separation and independent path reconstruction, found the 143-edge and 138-edge witnesses. The full-cube witnesses differ from the initial local forests. The independent verifier recounts all pairs, singleton squares and the two empty-square shares.

Their M12 pair shares are 48+29 and 25+17, giving charges 317 and 258. These values are independently enumerated; the current Lean witness modules certify path validity and singleton counts, not the share totals.

Two 30-second full-cube searches imposed at least 193 selected vertices together with equality in the corresponding pair bound. Both returned UNKNOWN without a candidate. No 192-edge construction or conditional exclusion follows.

## Reproduction

- `scripts/probe.py`: radius-four equality tests.
- `scripts/full_cube.py`: full-cube equality tests and cycle separation.
- `scripts/export.py`: orient the saved paths and generate Lean witness modules.
- `scripts/build.ps1`, then `scripts/check_constants.ps1`: fresh witness build and sharpness deductions.
- `scripts/length_probe.py`: the two bounded 192-edge tests.
- `scripts/verify.py`: independent evidence and axiom audit; saved in `data/verification.json`.

## Next direction

The count-only constants are now settled for these unrestricted pattern classes. Retain the empty-square term at equality: for pattern 0123415 and count sum 9, test whether the two M12 shares must sum to at least 12. If proved, the pair charge would be at least 228 (including the cases of count sum at least 10). This is an unproved target. Frequency/packing and boundary accounting would still be needed for a global improvement. Length-conditioned pair inequalities remain another possible route; the bank observations alone do not prove them.

Update: [milestone35](../35-equality-share-bonus/README.md) proves this target without the equality assumption and checks the occurrence overlap bound.
