# Six-centre parallel-share model: semantic audit

This is a source-level mathematical audit of the frozen `wincert.py` and
`share_enc.py`, not a completed Lean applicability theorem. Their exact hashes
are in `data/provenance.json`. Radius is three, six internal centres, cap 20,
`counter='stot'`, `exact=True`, alpha bounds `(0,21)`, endpoint budget two.
This is different from the radius-four corner-share model.

| Clause family / variable | Necessary assignment and reason | Formal status here |
|---|---|---|
| Selected vertex `X[v]`, window units | Membership in the translated/permuted snake; every window vertex selected | Existing general local-window framework available; new encoder not connected |
| `degree<=2` | An induced path has at most two selected neighbors at any selected vertex | Valid also at boundary, since omitting external neighbors only reduces degree |
| Interior `degree>=1` | Used only where all nine neighbors are in the ball; a nontrivial snake has no isolated selected vertex | Window contains eight vertices, so short-path exception does not arise in this local contradiction |
| Endpoint variable, `end_selected`, `degree1->end`, `end->degree<=1` | True exactly at selected vertices of global degree one; imposed only when full neighborhood is present | At most the two true path endpoints; no boundary endpoint is falsely charged |
| Endpoint sequential counter | Prefix threshold `s[i][j]` means at least `j+1` endpoint bits among the first `i+1`; budget two implies overflow clauses | Existing counter framework; full exact instance assignment still to connect |
| Singleton counts | For an internal centre, pairs using its two path directions cannot be singleton; the other 21 pairs are singleton exactly when the opposite corner is absent | In these share-only models `(0,21)` adds no count clauses. Count-chain instances require their own exact circuit and lumping audit |
| Four/six-cycle and saved cycle cuts | A selected cycle cannot lie in an induced path. Saved cuts have every vertex of degree two in the induced cut graph | Each generated model checks cut adjacency. To formalize: use arbitrary-length cycle exclusion, not merely a four-cycle argument |
| Empty square bit `E[Q]` | True iff all four selected-vertex bits vanish; both implication directions are emitted | All four corners lie within radius three of the relevant centre; no outside-square truncation |
| `g1`, `g3` | With the centre selected, let `n` count the other three parallel-square corners. Set `g1=E∧(n≤1)`, `g3=E∧(n=0)` | Unfixed, one-fixed, and two-fixed gate lemmas compiled in `ParallelShareTerm.lean` |
| Share unary leaves | `[E,E,g1,g3,g3,g3]` has weight 6, 3, or 2 for parallel-square selected count 1, 2, or 3 | `Snake9.LocalWindow.Axioms.parallel_unary_weight` compiled: count four is excluded from path acyclicity. Mapping concrete CNF leaf variables to these semantic bits remains |
| Omitted terms / fixed bits | An empty square meeting the fixed window has share zero. Fixed parallel-square corners make indicated gate bits zero | Fixed-count Boolean cases compiled; identification with concrete geometric terms remains |
| Totalizer tree, sequential centre merge | Output t is the semantic threshold on the exact sum of descendant leaf weights, clipped at cap+1 | `ParallelShareCounter.Circuit.satisfies` proves all merges and list indices in the abstract circuit; exact identification with emitted clauses remains |
| Overflow and truncated accumulator | Whole sum ≤ cap implies every prefix sum ≤ cap because all weights are nonnegative; discarded overflow threshold is false | `ParallelShareCounter.sequential_counter_sound` includes every intermediate overflow unit and trimmed accumulator; connect actual encoder trace next |

The path directions omitted from the share sum have a selected neighbor in the
corresponding square, hence zero contribution. For all remaining terms the three
parallel-square corners are at distance at most two from the centre; the empty
square corners are at distance at most three. Thus the boundary creates no missing
selected-vertex bit for these terms. No floor approximation is used: weights
6, 3, 2 are exact. Multiplicity is handled by the separate global share theorem.

`ParallelShareBridge.lean` now proves translation, coordinate permutation, and
reversal invariance of the full parallel-share sum. Its local-to-window theorem
still needs a `RefutedParallel` premise for the canonical model; this premise is
not obtained merely from the existing Boolean UNSAT theorem.
`ParallelShareIdentification.vertexShare_eq` and `share_eq_core` (in namespace
`Snake9`) identify the global and local parallel-share quantities exactly,
including at endpoints. These new proofs reuse generic cube-frame lemmas from
the corner-share development, not its different share identification.
The next formal step is an explicit satisfying-assignment construction for this
entire CNF, followed by exact model identification and all 34 shape refutations.

The new bridge/geometry/identification modules passed a hash-checked incremental
development build, with only the three allowed axioms in all printed audits.
This is not the required final fresh rebuild of the complete global theorem.

The local executable replay rejects RAT/negative hints rather than trusting them.
It has positive controls and corrupt-proof rejection controls. It remains
executable evidence until its input refutations are replayed by Lean's proved
checker. Raw CNFs, LRAT proofs, solver commands and tool/code hashes are retained.
