# Base-window source review

Status: bounded source and data audit passed. No mathematical scope or indexing
gap was found in the generated actual-snake statement. This review does not
replace the separate Lean checks, which were still controlled by the parent
agent. No solver or Lean process was run for this review. The short-window
export remains deferred.

## Exact reviewed sources

- `lean/ActualBase138.lean`: SHA256
  `c9178cc9493a09b34fdfde1ea3675ad2c5f213f7cfa658dd9fcf8cde2eca08ab`.
- `scripts/export_short.py`: SHA256
  `ffd40931387ea87812035f7afd5d3d02c5486719b28e37c74636a5043975decd`.
- `data/proof-plan-base.json`: SHA256
  `20863f459ee8cf7371783c1146b72bf28a8ea59d71161349a1bfea91bb0d5128`.
- `data/selected-core-semantics-base.json`: SHA256
  `bf9f29ce889a4edeaad9381cbc9fe0c5507e5668d8ad4de0f54b1fe66ed4ebd6`.

All 15 generated-source hashes and every source pin in the proof plan were
rechecked against the current files. This review did not modify them.

## Statement and count positions

The final theorem considers any actual nine-dimensional snake and any start
index for which all nine transitions fit. Its canonical transition word is
`012301430`, giving the ten vertices
`[0,1,3,7,15,14,12,28,20,21]` after a cube automorphism.

The generated bounds are indexed by the eight internal vertices. Bound index
`i` applies to the actual count at `r+i+1`, as in the existing bridge:

| Bound index | Actual position | Assumption |
| --- | --- | --- |
| 0 | r+1 | between 0 and 21 |
| 1 | r+2 | between 0 and 21 |
| 2 | r+3 | between 6 and 21 |
| 3 | r+4 | equal to 3 |
| 4 | r+5 | equal to 3 |
| 5 | r+6 | equal to 3 |
| 6 | r+7 | equal to 5 |
| 7 | r+8 | equal to 2 |

The six row symbols therefore apply exactly at offsets 3 through 8. The
symbol 6 is interpreted as a lower bound. The first two counts are unrestricted
within their ordinary range. The fitting condition makes every one of these
positions internal, so the existing bound of 21 applies. There is no use of
an out-of-range direction or count and no restriction on whether the window
touches either path endpoint.

The normalization obtains a permutation from the actual canonical transition
sequence. It proves the required direction identity at every offset before
calling the existing actual-snake bridge. It does not assume that the actual
coordinates already have the displayed labels. The vertex list, its nine
transitions, and the number of bounds agree.

## Endpoint, parity and proof premises

The only endpoint condition in the encoding is the ordinary global budget of
at most two endpoint flags, with the usual degree interpretation. The actual
snake bridge supplies these properties from the path. There are no forbidden
endpoint locations, parity clauses or assumed endpoint distances. The fitting
condition implies the path has positive length; no even-length or odd-length
hypothesis is present.

The base CNF contains the standard degree constraints, counters and ordinary
square/six-cycle clauses. It has no appended cycle cuts. All clauses are
interpreted through the existing snake axioms, including acyclicity. The final
actual-snake theorem takes neither a refutation nor a satisfying-assignment
interpretation as an external assumption: both are assembled from its
generated dependencies. Their compilation remains a separate obligation.

## Variable and counter audit

A separate read-only Python check compared the saved encoding, semantic
receipt and generated Lean text without invoking either exporter or solver.
It verified the following:

- The variable map and inverse are a bijection on all 4,568 variables.
- Every saved original variable meaning maps to the correct new variable.
- All 12 counter lists preserve literal signs, order and multiplicity, their
  thresholds and their kinds. Register meanings preserve their counter index
  and both register coordinates.
- The generated Lean meaning tree was parsed and all 4,568 entries were
  checked against the semantic receipt; variable zero remains unused.
- Every generated counter entry and all 2,353 ordered semantic tags match the
  receipt. The complete generated raw CNF matches the recorded signed clauses
  after the documented literal encoding.
- Every selected signed clause is the image of its original clause under the
  same bijection. The exporter also checks exact full-CNF reconstruction,
  original core IDs, inverse renaming of proof clauses, unchanged proof IDs
  and hints, and packed replay.

Only 1,485 variables occur in the selected core and retained proof. These
occupy the initial variable range, below the checker offset 2400. The remaining
semantic entries can have larger indices: they are evaluated by the ordinary
semantic table and are absent from the packed proof. This distinction does
not truncate any counter or change a meaning.

The selected core uses counter indices `0,2,3,4,5,6,7,8,9,10,11`. Counter 0
is the endpoint budget. The remaining used counters give both bounds at
internal centre indices 3 through 7. Counter 1, encoding the preceding lower
bound 6, is unused by the core. It remains in the generated semantic table,
whose generic check validates every counter. The final theorem consistently
retains the original lower-bound hypothesis; removing it would require an
explicit semantic specialization and a separately checked statement.

## Scope

Successful Lean checking of the pinned chain would prove exclusion of this
specific canonical row in every actual snake. It would not establish the
stronger short-window upper-cap statement, a new minimum cycle mean, or a new
global bound. Those conclusions require their respective additional steps.
