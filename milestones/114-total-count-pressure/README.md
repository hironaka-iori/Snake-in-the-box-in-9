# Milestone 114: total-count pressure and a replayed native certificate

The proposed restriction is that the five internal counts on canonical
directions `012310` sum to at least 19, with no further count caps.
The native contradiction for a total at most 18 has now been independently
replayed. The selected certificate uses 5,206 input clauses, 358,464
deductions and 22,088,504 propagation hints. Both the selected-core and
original-CNF identifier versions derive the empty clause.

The full concrete certificate has not passed Lean. Lean checks its
geometric transfer under an explicit local contradiction premise, and
three arithmetic lemmas for the existing global comparison. This round
has two successful Lean modules, four standard axiom reports and no new
mathematical definitions.

Adding the candidate to the previous rule family removes 2,263 further
graph keys and raises the completed-floor minimum mean from 484 to 484.8.
The integer comparison remains 235. The conditional-floor comparison
remains 234. A stronger hypothetical total lower bound of 20 only improves
the first potential range; its local solver result is UNKNOWN. No new
global upper bound is established.

Read `mathematical-note.md`, `data/proof-summary.json` and
`audit/final-review.md`. The exact graph comparisons and replacement cycles
are recorded under `data/total19/` and `data/total20-hypothesis/`.
`data/checkpoint.json` and `data/file-manifest.json` freeze the round.

## Selected certificate and reproduction

- `work/012310-total18/full.cnf` is the original formula, including eight
  directly verified induced-cycle cuts. Its sum counter has 105 occurrences
  and 84 distinct literals; multiplicity must be preserved.
- `work/012310-total18/full.trim.lrat` is the selected proof mapped back to
  original clause identifiers. Metadata are in
  `data/012310-total18-certificate.json`.
- `scripts/replay_core.py` implements the completed two-stage native RUP
  replay. The existing outputs are immutable; use a new output location
  for reproduction or further refinement.
- The alternative pool of 115 valid cycle exclusions produced a larger
  retained certificate, with 29,534,822 hints. That alternative is
  unselected and has not been independently replayed.
- Large proof files are retained locally and also saved as verified gzip
  archives. Run `scripts/verify_saved.py --restore-archives` on a fresh
  checkout before accessing missing large originals. Use `--verify` for
  the frozen manifest.

Writing the selected native proof through system temporary storage
completed in 20.656 seconds after the same formula/options timed out at
60 seconds on the research volume. The completed proof shares the exact
40,935,424-byte prefix of the timed-out attempt. Future large proof output
should use temporary storage followed by a verified copy into this folder.

## Continuation

First reduce the selected proof's cost and export its concrete sum
semantics and contradiction to Lean. Milestone 112 supplies a working
export/replay pattern. This case additionally needs its eight cycle tags
and all five count centres. Preserve the original certificate if a
refinement fails or grows.

After advancing that obligation, the shared remaining local target is
`012345`: exact tuples `(4,3,3,5,4)`, `(5,4,2,5,5)` and `(5,4,3,4,5)`.
The broader middle-at-most-3, total-at-most-21 cell is untested.

The interrupted milestone 104 module passed unchanged on retry, and the
existing batch resumed from checked receipts. Its observation is dated;
verify the live process before acting. Paper revision 106 is unchanged,
and the next full revision remains 116. The maintained interval is 191
through 235 edges, with a complete independent rebuild pending.
