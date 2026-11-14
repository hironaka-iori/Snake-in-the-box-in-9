# Exclusion of the first-priority six-coordinate repair

**Theorem (computer-assisted).** No 192-edge induced path in the nine-cube agrees with the entry-87 candidate on bits 0, 2 and 3 at every index.

The six free coordinates are 1, 4, 5, 6, 7 and 8. Of the 192 transitions, 93 change only free coordinates, giving 94 chronological intervals. The first bounded SAT screen left this case open. Two trace cliques give a stronger formulation.

| Interval parity | Pairwise conflicting anchors | Available words | Maximum absent from anchor family |
|---|---:|---:|---:|
| Even | 30 | 32 | 2 |
| Odd | 28 | 32 | 4 |

For a clique of k intervals, the free words assigned to its members are all different. Its image uses exactly k of the 32 words of that parity. For each parity word w introduce an indicator which is true precisely when an anchor is given w. Require at most 32−k absent indicators. This is an exact consequence of the clique constraints. The remaining intervals may use any compatible word, including a word absent from that clique. The normalization translates the initial word to zero and renames free coordinates in order of first use. [The two clique lists](deep-145678.json) and [the implementation](solve.py) give the full instance.

Lean checks the generic interval-parity recurrence and the missing-word inequality in [TraceParity.lean](TraceParity.lean). CaDiCaL refuted the resulting finite formula. An independent DRAT checker accepted its proof, using 294,452 core lemmas and 30,309,940 resolution steps. The [certificate receipt](certificate-145678.json) records the input and proof hashes. [Archive of the formula](certificate-145678.cnf.gz) and [archive of the proof](certificate-145678.drat.gz).

To reproduce, run `python rerun_deep_certificate.py deep-145678.json --checker /path/to/drat-trim`. Add `--replay-only` to check the archived bytes and skip generation. The replay verifies all pairs within both trace cliques and the hashes before verifying the Boolean refutation. The input-to-model geometric correspondence is the written one in [the proof note](README.md).

## Fixed coordinates 2, 3 and 4

The same method excludes free coordinates 0, 1, 5, 6, 7 and 8. Here the even clique has 26 anchors and the odd clique has 32. The even clique can leave at most six words absent from its image; the odd clique must use every odd word. The [two clique lists](deep-015678.json) and [independent checker receipt](certificate-015678.json) record the case. The proof core used 451,333 lemmas and 54,979,221 resolution steps. It is the fourth certified six-coordinate exclusion on this branch. The compressed proof is distributed in consecutively numbered gzip members alongside the [Boolean formula](certificate-015678.cnf.gz). The replay command above accepts `deep-015678.json` and reads the pieces in order.
