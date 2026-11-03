# Milestone 132: a parity-free endpoint consequence

A new local theorem has passed the complete Lean check. In any snake in Q9,
a fitting canonical 012032 window with second-plus-fourth internal count at
most nine forces one endpoint to be at Hamming distance two from both counted
centres. There is no length-parity assumption. Consequently the pair sum is
at least ten whenever neither endpoint has those two distances.

The proof includes all 51 certificate modules, the interpretation of all 683
selected clauses for an actual snake, and the final coordinate transfer.
It preserves the 42 corner occurrences, including five vertices counted twice.
The final statements use only the standard Lean axioms recorded in their logs.
The two failed semantic attempts and the successful checks are saved.

This is an unconditional local result. It supplies no new global upper bound.
The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. The optimum and
the proposed value 196 remain unresolved.

A separate Lean-checked arithmetic result limits the current uniform-credit
approach. The two surviving cycle constraints keep its comparison above 235
when the endpoint-event allowance is at least two. This limitation concerns
the stated fixed model and formula. It does not rule out sharper geometric
restrictions or a revised graph that excludes other surviving cycles.

Next: use the endpoint theorem to study how low-pair windows can occur along
one actual snake. The earlier bound of thirteen windows requires proximity
to BOTH endpoints and cannot be reused for this one-endpoint conclusion.
Retain the seven-edge competing cycle when testing any proposed improvement.
No new mathematical definition is introduced. Paper revision 126 is unchanged;
the next scheduled full paper revision is136.

## Evidence and continuation

- MATHEMATICAL_NOTE.md gives the theorem, proof structure and numerical limit.
- lean/ActualEndpoint132.lean states the actual-snake conclusions.
- data/ActualEndpoint132-audit.json records the successful combined check.
- data/replay-progress.json records the complete 51-module refutation.
- audit/endpoint-core-review.md and audit/endpoint-export-review.md distinguish
  independent original-clause and export reviews.
- work/certificate contains the native certificate and exact selected clauses.
- data/semantic-preparation.json preserves the initial source preparation;
  data/semantic-repair2.json records the corrected source and initial failures.
- data/independent-credit-audit.json and audit/credit-limitation.md record the
  conditional arithmetic limitation and its cycle premises.
- data/verification.json, checkpoint.json and file-manifest.json fix saved scope.

Keep failed attempts and exact snapshots. Do not restart the completed 132
search, replay or semantic checks. Inspect the separate live 115 job before
any restart. Paper revision 126 remains unchanged, with revision 136 next.
