# Coverage of seven-transition windows

Independent enumeration confirms exactly **34** canonical induced seven-transition
words. Reversal reduces them to **21** classes: eight words are unchanged after
reversal and canonicalization, and the other 26 words form thirteen pairs. The
saved path bank contains every one of these 21 classes.

## Independent finite enumeration

The audit enumerates all $7^6=117649$ words of length seven whose first coordinate
is zero. It retains exactly the 877 words unchanged by canonicalization. It then
constructs the eight successive vertices by coordinate flips and directly checks
distinctness and every pairwise adjacency. Exactly 34 words remain. Their ordered
list agrees with all three saved lists: `data/cases.json`, `data/six/shapes.json`,
and the literal list in `FamilyCoverage.lean` from milestone 32.

The enumeration imports no earlier enumerator or graph code. A seven-transition
word uses at most seven distinct coordinates, so this enumeration covers the
canonical direction words of such windows in the nine-dimensional cube. Every
canonical reverse is in the same 34-word list, and reversing and canonicalizing
twice returns the original canonical word.

## Saved Lean evidence and its limits

The earlier coverage sources have the following relevant statements:

- `FamilyCoverage.lean`: `coverage_table` checks the finite table;
  `classified` places a canonical induced word in that table; and
  `patterns_valid` checks the listed words.
- `ParityCoverage.lean`: `normalized_covered` transfers the classification through
  coordinate canonicalization.
- `SnakeCoverage.lean`: `snake_pattern` states that every fitting seven-transition
  window of a snake has its canonical word in the 34-word list.
- `SnakeCoverage.lean`: `no_six_fours_of_refuted` uses 34 explicit refutation premises
  for six counts all equal to four. Its conclusion concerns that exact tuple.

The three saved bridge logs contain eight printed axiom reports, all limited to
`propext`, `Classical.choice`, and `Quot.sound`. Corresponding compiled objects
exist in the saved isolated build. The current `FamilyCoverage` source matches
its archived LF-normalized source-manifest hash. The nine archived normalization
support sources also match their saved LF-normalized hashes.

The older proof-verification file reports 18 audits, including four individual
count-four refutations. It does not bind the coverage bridge sources and objects
with paired historical hashes. In particular, `ParityCoverage` and
`SnakeCoverage` are absent from both its source-hash map and the earlier source
manifest. This audit therefore records the current source, object and log hashes
and the preserved successful-check evidence, without claiming a new compilation
or a newly reconstructed source-to-object verification chain. No compiler,
solver or contradiction replay was run here.

The earlier actual-snake classification can support a sum-based proof, but the
exact-four contradiction theorem does not establish a six-count sum lower bound.
A universal bound of 25 or 26 still requires the corresponding count-sum
refutations, multiplicity-preserving semantics, and transfer to actual snakes.
Certifying only the 21 representatives additionally requires a checked reversal
argument for the sum and its placement. The count sum is unchanged by reversing
the six positions; that observation must be included in the proof that joins
the representative cases.

## Coverage of the saved path bank

All 21 classes occur in the pinned milestone-123 scan of 134 paths. The table
below reproduces that scan's reported minima. This audit independently rechecks
each displayed attaining window: directions, canonical shape, six singleton-square
counts, and their sum. The witnesses occupy 12 distinct saved paths; checking
those paths requires 220,032 pairwise adjacency tests, all of which passed.

These checks verify the displayed witnesses. The assertion that they are the
minima over the entire bank comes from the pinned prior scan, whose source and
input hashes were checked. The present audit does not repeat that whole-bank
minimization. Even a complete finite-bank minimum cannot prove a universal bound.

| Canonical representative | Original case indices | Minimum reported in saved bank |
|---|---|---:|
| $0120310$ | 0 | 46 |
| $0120314$ | 1, 24 | 37 |
| $0120324$ | 2, 16 | 45 |
| $0120340$ | 3 | 43 |
| $0120341$ | 4, 20 | 48 |
| $0120342$ | 5, 11 | 39 |
| $0120345$ | 6, 32 | 41 |
| $0123014$ | 7, 23 | 31 |
| $0123024$ | 8, 15 | 36 |
| $0123041$ | 9, 19 | 56 |
| $0123042$ | 10 | 43 |
| $0123045$ | 12, 31 | 38 |
| $0123104$ | 13, 27 | 37 |
| $0123140$ | 14, 26 | 38 |
| $0123145$ | 17, 28 | 39 |
| $0123401$ | 18 | 60 |
| $0123405$ | 21, 30 | 53 |
| $0123410$ | 22 | 49 |
| $0123415$ | 25 | 43 |
| $0123450$ | 29 | 51 |
| $0123456$ | 33 | 52 |

The smallest reported value is 31, on $0123014$. No seven-transition shape is
missing from the bank, but the bank contains only selected paths. Therefore
neither 31 nor a smaller proposed universal floor is proved by its coverage.

## Reproduction and preserved evidence

`data/coverage-audit.json` records the 34 words, all reversal classes, the eight
axiom reports, the source/object/log hashes, the nine normalization source hashes,
and the reconstructed minimum witnesses. `scripts/audit_coverage.py` prints a
summary; `--output` creates a new evidence file exclusively. It changes no prior
files and invokes no compiler or solver.

Evidence hashes:

- `data/coverage-audit.json`: `9a86a8cfc4be239177f1e9712aaf587d7cba02f5ce68701dd0cba4d0b0ae2f32`.
- `scripts/audit_coverage.py`: `bc0eb961cbabdbec5fd57125d2a1a5b6f3e17fb30cfc806576bab87818ad3ba5`.
