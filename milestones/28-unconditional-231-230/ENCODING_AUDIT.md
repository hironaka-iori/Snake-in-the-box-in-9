# Six-centre parallel-share model: semantic audit

This audits the frozen `wincert.py` and `share_enc.py`. Generic clause soundness
and the full applicability theorem for case 01 are now checked in Lean; the
other 33 concrete share instances remain to be checked. Their exact hashes
are in `data/provenance.json`. Radius is three, six internal centres, cap 20,
`counter='stot'`, `exact=True`, alpha bounds `(0,21)`, endpoint budget two.
This is different from the radius-four corner-share model.

| Clause family / variable | Necessary assignment and reason | Formal status here |
|---|---|---|
| Selected vertex `X[v]`, window units | Membership in the translated/permuted snake; every window vertex selected | Existing local-window checker is integrated under the same assignment; case 01 passed |
| `degree<=2` | An induced path has at most two selected neighbors at any selected vertex | Valid also at boundary, since omitting external neighbors only reduces degree |
| Interior `degree>=1` | Used only where all nine neighbors are in the ball; a nontrivial snake has no isolated selected vertex | Window contains eight vertices, so short-path exception does not arise in this local contradiction |
| Endpoint variable, `end_selected`, `degree1->end`, `end->degree<=1` | True exactly at selected vertices of global degree one; imposed only when full neighborhood is present | At most the two true path endpoints; no boundary endpoint is falsely charged |
| Endpoint sequential counter | Prefix threshold `s[i][j]` means at least `j+1` endpoint bits among the first `i+1`; budget two implies overflow clauses | Existing counter framework; full exact instance assignment still to connect |
| Singleton counts | For an internal centre, pairs using its two path directions cannot be singleton; the other 21 pairs are singleton exactly when the opposite corner is absent | In these share-only models `(0,21)` adds no count clauses. Count-chain instances require their own exact circuit and lumping audit |
| Four/six-cycle and saved cycle cuts | A selected cycle cannot lie in an induced path. Saved cuts have every vertex of degree two in the induced cut graph | Each generated model checks cut adjacency. To formalize: use arbitrary-length cycle exclusion, not merely a four-cycle argument |
| Empty square bit `E[Q]` | True iff all four selected-vertex bits vanish; both implication directions are emitted | `ParallelShareBoolean.square_eval` identifies the Boolean formula; two exact core clauses checked in `ParallelShare01GatePilot`. All instances and their shared assignment remain to integrate |
| `g1`, `g3` | With the centre selected, let `n` count the other three parallel-square corners. Set `g1=E∧(n≤1)`, `g3=E∧(n=0)` | Unfixed/fixed gate lemmas and formula identification compiled. Four exact `g1` core clauses passed `checkClauses_sound`; the pilot core has no `g3` clauses |
| Share unary leaves | `[E,E,g1,g3,g3,g3]` has weight 6, 3, or 2 for parallel-square selected count 1, 2, or 3 | `Snake9.LocalWindow.Axioms.parallel_unary_weight` compiled: count four is excluded from path acyclicity. Mapping concrete CNF leaf variables to these semantic bits remains |
| Omitted terms / fixed bits | An empty square meeting the fixed window has share zero. Fixed parallel-square corners make indicated gate bits zero | Fixed-count Boolean cases compiled; identification with concrete geometric terms remains |
| Totalizer tree, sequential centre merge | Output t is a threshold of the sum of actual geometric terms in its recorded block | `ParallelShareClauses.mergeCheck_sound` checks concrete input/output meanings and disjoint blocks. All 60 such clauses in case 01 passed |
| Overflow and truncated accumulator | Whole sum ≤ cap bounds every recorded term block because the term list is a sublist of all window terms | `ParallelShareBlocks.blockMass_cap` and `ParallelShareClauses.boundCheck_sound` prove this for arbitrary checked blocks; case 01's overflow unit passed |

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
`ParallelShareCertificate.sound` now constructs one assignment for all accepted
clause families. `LocalWindowSat.ParallelShare01` checks all 81 exact core clauses,
the variable meanings and the term sublist, then combines them with the existing
kernel refutation. This proves `RefutedParallel` for case 01. Exact instance
identification and the refutations for the remaining shapes still have to finish.

The new bridge/geometry/identification modules passed a hash-checked incremental
development build, with only the three allowed axioms in all printed audits.
This is not the required final fresh rebuild of the complete global theorem.

The six gate clauses of the committed `ParallelShare01` core now have a kernel
applicability proof, under only the displayed window-selection premise and the
explicit meanings of the compact variables. The source references the committed
core data directly. A deliberately corrupted first clause is kernel-checked to
be rejected. The later full pilot extends this to all 81 core clauses under one
assignment, without relying on this earlier six-clause test as a substitute.

The full pilot and arbitrary-window application passed a fresh build of all 29
custom modules from commit `504a29de6a19e9accfe07bd46d1e61e9bdf2b439` in an
isolated custom source directory. The final theorems use only the three allowed
axioms. This independently validates one shape, not the whole 34-shape family or
the unconditional global bound. The complete receipt is
`data/parallel-share-full-pilot-fresh.json`.

The generalized `generate_parallel_cases.py` keeps every compact core variable
unchanged and allocates additional IDs for counter inputs omitted from the core.
This preserves the complete endpoint prefix-counter semantics in the same
assignment. All used clauses are traced to the full hash-matched encoder;
saved cycle cuts use the existing arbitrary-cycle tag. A binary meaning tree
and the proved `checkRaw_flatMap` combine 128-clause shards without changing
their assignment. The generated `exact_raw` theorem checks the concatenation
against the original compact CNF in Lean. The generalized case 01 has passed;
case 00 has passed its data checks and representative clause shards, with the
full run pending. `runtime/applicability/state.json` records the frozen batch.
Its `refuted_of_unsat` theorem is deliberately a conditional interface: completed
applicability cases must still be joined to the matching Boolean refutations.

The local executable replay rejects RAT/negative hints rather than trusting them.
It has positive controls and corrupt-proof rejection controls. It remains
executable evidence until its input refutations are replayed by Lean's proved
checker. Raw CNFs, LRAT proofs, solver commands and tool/code hashes are retained.

`CountWindowPairs231.table_checked` checks the actual packed two-centre table
at threshold 8, over every positive symbol pair. Its accepted covering keys
are `(1,1)`, `(1,2)`, `(1,3)` and `(1,4)` with exact count intervals, including
reversal. The shape proof covers every valid three-edge window. The compiled
`hw2_of_pairs` uses the same `countSeq`, `pathDir` and packed-table functions as
the conditional 231 aggregate, with the four refutations still explicit.
The 181-module hash-validated development closure and allowed-axiom audits
are recorded in `data/count-window-pairs-development.json`. This is a table
and semantic bridge, not a substitute for the remaining concrete refutations
or the final independent fresh rebuild.

After case 00's `Check44` timed out, the stopped batch's unfinished checks
were split into 16-clause slices. The original Data and CNF files are unchanged.
Each slice uses the original `checkRaw`; the replacement theorem has the exact
original statement, and `rfl` validates concatenation of its take/drop slices.
Completed modules are retained only through the existing dependency-hash checks.
The original source, receipt and failed log were archived before replacement;
the refinement script's committed source and hashes are recorded separately in
`data/applicability-shard-refinement.json`. Split-module progress alone does not
establish the whole case's geometric applicability.

`CountWindowTable231.no_window` separates complete finite coverage from the
required local refutation family at any window length. Positive symbols cover
every actual internal count after truncation to 8. Canonical relabelling and
reversal preserve both the original packed-table lookup and interval matching.
`CountWindowTriples231.table_checked` applies this to the exact 91 three-centre
keys from the frozen source set, and `hw3_of_triples` has the original aggregate
premise's functions and indices. All printed axioms are allowed. These results
are conditional on the concrete interval refutations, whose completion must be
audited separately.

`CountWindowTablePrefix231.no_window` proves that splitting by the first two
positive symbols loses no sequence: the checked prefix and suffix concatenate
to the original symbol list. The larger tables have all 64 prefixes for each
of the five- and six-centre lengths. Their frozen concrete checks are pending;
the compiled generic bridge alone is not evidence that those checks succeed.

Applicability case 00's final source and all direct dependency closure hashes
were identical before and after adding a 64 MiB Lean thread stack. The repaired
final module passed, and both exported targets have only allowed axioms. The
archived failure, successful command and exact comparison are recorded in
`data/applicability-case00-stack-repair.json`; no failed audit was accepted.
