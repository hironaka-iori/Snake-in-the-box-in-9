# A second six-coordinate exclusion and the five-coordinate replay

**Result.** No entry-87 repair can retain coordinates 0, 2 and 4 throughout. This excludes the six free coordinates 1, 3, 5, 6, 7 and 8. The [explicit refutation](certificate-135678.drat.gz) and its [Boolean formula](certificate-135678.cnf.gz) are independently replayable.

## Why equality helps

There are 32 odd intervals whose traces conflict pairwise. Their indices are in the [certificate receipt](certificate-135678.json). The trace lemma forces different words on all 32, so they use every word of the common six-bit parity class exactly once. The initial word can be translated to zero, making this the odd parity class. For each odd word, the formula adds one clause requiring its occurrence among the anchors and pairwise clauses requiring that it occur at most once. These are consequences of the geometry. CaDiCaL then refutes the full indexed path model. The independent DRAT checker accepted the refutation. The core used 171,604 proof lemmas and 13,431,154 resolution steps.

The translation, canonical first-use ordering, contraction to chronological intervals and distance encoding are given in the [search program](solve.py) and the [proof note](README.md). The SAT values are one-hot free words. For every binary relation, each selected word must have compatible support in the other domain. The two directional support encodings are equivalent to that relation because each domain has exactly one selected word. For a path of 193 vertices the model checks every indexed pair during construction, including pairs in the same interval. The DRAT check proves the emitted Boolean formula unsatisfiable; the proof of the formula's correspondence to a geometric realization is written here and in the note.

The same equality criterion applies to five free-coordinate sets in the [saturation table](saturation.json). It gives an additional necessary condition: if a word of the opposite parity is used by an interval, exactly six of the 32 anchors carry its neighbours. Two different words of that opposite parity have at most two common neighbours, since a two-step cube path between distinct words must flip two distinct coordinates and the two orders are the only possibilities. The table records possible and required anchor neighbours. The UNSAT formula above adds the explicit one-to-one occurrence clauses; it does not depend on the neighbourhood comparison.

## Independent proof replay

Use the repository's [drat-trim source](../keep96/vendor/drat-trim/drat-trim.c), Git blob `cf8a676ffcc7ef5a47124bbafc9b680a2df333e0`. The Windows executable used LLVM MinGW with `-O2 -Dgetc_unlocked=getc`. From this directory run `python certificate.py --checker /path/to/drat-trim --use-archive`. This checks all 496 anchor pairs, decompresses the files, verifies both SHA-256 digests and requires the checker's explicit VERIFIED result. Omitting `--use-archive` regenerates the search artifacts using python-sat 1.9.dev17.

For the five-coordinate result, a separate run generated and independently checked all 126 DRAT proofs with the same checker. All passed. The [per-mask receipt](five-verified.json) records the individual CNF and proof hashes and byte sizes. Reproduce this with `python recheck_five.py --checker /path/to/drat-trim --output replay-five.json`. The optional `--retain DIRECTORY` saves the individual uncompressed files.

The two established six-coordinate exclusions have fixed triples {0, 1, 4} and {0, 2, 4}. The 84-case [initial bounded screen](six-screen.json) returned OPEN on every case. In the [strengthened five-case run](saturated-search.json), one case was excluded and the other four reached the conflict limit.
