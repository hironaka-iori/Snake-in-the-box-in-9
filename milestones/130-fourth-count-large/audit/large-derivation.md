# The fourth-count constraint and its concrete clauses

Both semantic modules passed Lean. For an actual snake and a fitting window
whose canonical direction sequence is \(0120324\), the hypothesis
\(\alpha_{r+4}\ge4\) implies that at most seventeen of the fourth centre's
twenty-one opposite corners are selected. The concrete result supplies a
coordinate permutation and proves satisfaction of exactly the 717 added
counter clauses.

The hypotheses are the actual snake, the fitting window, its canonical word,
and the fourth-count lower bound. The proof requires no six-count total cap,
pair-count inequality, or equality-case lower bounds for the first and second
counts.

## Count conversion

In canonical coordinates the window vertices are

\[
0,1,3,7,6,14,10,26.
\]

The fourth centre is vertex 6, with incident path directions 0 and 3. Its
twenty-one opposite corners arise by choosing two of the seven unused
directions. Lean checks the explicit corner list against that construction.
The selected and absent counts add to twenty-one. The established frame
identity identifies the absent count with \(\alpha_{r+4}\), giving

\[
\#\{\text{selected opposite corners at the fourth centre}\}
+\alpha_{r+4}=21.
\]

Consequently \(\alpha_{r+4}\ge4\) gives the selected-corner cap seventeen.
The normalization theorem constructs the required coordinate permutation
from the canonical direction-word hypothesis.

## Concrete added clauses

The semantic certificate retains counter index 9, the twenty-one primary
inputs and all 357 fresh registers numbered 8706 through 9062. The nine
preceding counter entries are empty defaults because their clauses are
outside this certificate. All 512 primary meanings remain present. No older
auxiliary register occurs in the checked 717-clause list.

Lean checks every literal meaning and all clause tags. The clause checks are
split into twelve groups of at most 64 clauses, then assembled into the exact
raw clause list. Counter-tag validity is independent of the window argument.
The count conversion supplies the counter bound; the existing clause
soundness theorem supplies satisfaction under the actual normalized
assignment. The final theorem constructs the normalization and concludes
satisfaction of the added clauses directly from the stated actual-window
hypotheses.

A separate parser checks the saved Lean raw lists, tags, counter literals and
every meaning index from 0 through 9062 against the counter metadata and the
last 717 clauses of the saved search input. This verifies the data connection;
the mathematical interpretation is supplied by the successful Lean checks.

## Successful checks

| Module | Public reports | Elapsed seconds |
|---|---:|---:|
| `LargeLower130` | 5 | 201.562 |
| `LargeClauses130` | 5 | 60.375 |

All ten reports contain only subsets of `propext`, `Classical.choice` and
`Quot.sound`. The concrete literal check has no axioms. Source bytes,
compiler logs, object bytes, dependency pins and checker snapshots were
verified against the successful receipts. Both checks passed their fresh
resource gates before launch. No failed Lean attempt occurred in this task.

The stable receipts are `data/independent-large-lower-audit.json` and
`data/independent-large-clauses-audit.json`. The combined verification is
`data/large-semantics-verification.json`; the exact Lean-data comparison is
`data/lean-data-review.json`. The interrupted earlier draft of
`LargeLower130.lean` was preserved without modification. Historical generator
records retain their original generated-but-not-yet-checked status; these
successful receipts provide the later checked status.

## Scope

This result justifies the 717 clauses appended to the existing 104529-clause
input. Satisfaction of the complete 105246-clause conjunction and any
contradiction of it remain separate proof obligations. Neither a new
six-count lower bound nor a new global upper bound follows from this semantic
result alone.

## Fixed source and receipt hashes

| Evidence | SHA256 |
|---|---|
| LargeLower130 source | `409e774f6e9afd78a5c7a329e9a90e6b13176aa2d76cf41c02fe83e7bb0d73ac` |
| LargeLower130 object | `c567b6b10b8a739bb6f39920172ca604984cc5a9ae62a954e60f678303084076` |
| LargeLower130 receipt | `ea9c2ecc611f904b21a6cd5afe424a40c58dc784d57697f82c384e5235811798` |
| LargeClauses130 source | `b93ed3342b715a60b03daf129f957cf413563968584ebf2041bc087d2e790d4e` |
| LargeClauses130 object | `21fe6ab9ca5689e25716615c09f830b06f85c0dec57d10b0eb6b1867d5fa2834` |
| LargeClauses130 receipt | `f24ab057716669c85530df69aff15b083117ac6d11c92e983901b8261522c38b` |

The combined verification record's SHA256 is `1db8942d5f198704cff88b54819e746fb13c055d69acad1b30b316ff47d0e87a`.
