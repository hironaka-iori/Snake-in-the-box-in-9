# Concrete core semantics and conditional deductions

The actual-snake interpretation of the fixed 3500-clause core is checked.
For every actual snake and every fitting window with canonical transition
word \(0120324\), the hypotheses
\[
\alpha_{r+4}=3,
\qquad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\leq11
\]
imply that the exact selected CNF has a satisfying Boolean assignment.
`actual_satisfies_core` proves this statement with all finite metadata and
clause checks discharged. It has no pending refutation premise, no six-count
cap, and no pair-inequality premise.

## Interpretation of the selected clauses

The fixed CNF source is
`lean/Recovered129G/LocalWindowCnf/Triple129.lean`, in namespace
`Snake9.LocalWindow.Triple129`. It was compiled without modifying its source.
The semantic module imports that exact declaration and checks its 3500
clauses against the saved tags in 55 groups of at most 64 clauses.

The concrete finite checks establish:

- Every ordinary counter is valid for the normalized window with intervals
  \([(0,21),(0,21),(0,21),(3,3),(0,21),(0,21)]\). The active ordinary
  counters are indices 0, 4, and 11: endpoint count at most two, fourth count
  at least three, and fourth count at most three.
- Counter 12 consists of negative primary literals. Its vertex list is a
  permutation of the three opposite-corner lists at normalized centres
  \((7,2,0),(14,3,2),(10,2,4)\), with all 63 occurrences retained. Its
  stored upper bound is 11.
- Every selected clause passes the existing tag checker. The unused counter
  entries are empty default entries. No total-count counter, pair counter,
  or strengthened first/second counter is used by this certificate.

The meaning table retains 2415 variable meanings although the CNF uses 1695
proof variables. The additional meanings preserve primary and endpoint
inputs required by the retained counters even when those inputs do not occur
in the surviving clauses. Certificate data are noncomputable Lean
declarations, and the finite checks use kernel reduction.

The already checked canonical-frame construction places the actual window
at \(0,1,3,7,6,14,10,26\). Its window axioms justify the ordinary counters.
Exact count transport identifies the three absent-corner counts with
\(\alpha_{r+3},\alpha_{r+5},\alpha_{r+6}\). Their assumed sum cap supplies
the remaining counter condition. The existing clause-soundness theorem then
constructs an assignment satisfying the exact imported CNF.

## Deductions requiring the refutation

The two remaining public results take the explicit premise
`Unsat Triple129.cnf`. This premise states unsatisfiability of the exact
selected CNF and is the obligation for the separate LRAT replay.

With that premise, `actual_triple_lower` proves
\[
\alpha_{r+4}=3
\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\geq12
\]
for every fitting actual window of canonical shape \(0120324\). The proof
assumes a sum at most 11 and contradicts the checked satisfying assignment.
It uses no six-count cap or pair inequality.

With the same unsatisfiability premise, `actual_six_lower` proves
\[
\alpha_{r+4}=3
\quad\Longrightarrow\quad
\sum_{j=1}^{6}\alpha_{r+j}\geq23.
\]
For the canonical prefix \(012032\), the checked first/fourth exclusion
gives \(\alpha_{r+1}\geq3\), and the checked pair inequality gives
\(\alpha_{r+2}\geq5\). Adding these to the fourth count 3 and the
three-count lower bound 12 gives \(3+5+3+12=23\).

The standard axiom reports do not discharge the explicit unsatisfiability
premise. Until the separate refutation is supplied, these two lower bounds
remain conditional. This semantic certificate alone proves no new global
upper bound.

## Verification and fixed evidence

The unchanged CNF declaration passed in 12.687 seconds. The semantic module
passed its first launched check in 269.968 seconds, within a 600-second wall
allowance. The latter launch passed the resource gate with 2.64 GiB free and
two other Lean processes. All source, checker, and dependency hashes were
verified unchanged after compilation.

Six public reports were checked:

- `ordinary_checked`: `propext`, `Quot.sound`.
- `triple_checked`: `propext`, `Classical.choice`, `Quot.sound`.
- `tags_checked`: `propext`.
- `actual_satisfies_core`: the three standard axioms above.
- `actual_triple_lower`: the same standard axioms, with `Unsat` an explicit
  theorem parameter.
- `actual_six_lower`: the same standard axioms, with `Unsat` an explicit
  theorem parameter.

The stable receipts are `data/independent-core-cnf-audit.json` and
`data/independent-core-semantics-audit.json`. Each is an exact copy of its
successful attempt record. Paths in these records are absolute.
`object_sha256` identifies the timestamped object;
`importable_object_sha256` identifies the reusable object at
`importable_object`. The records use `log_sha256` and a `dependencies`
mapping, and do not use an `olean_sha256` field.

| Evidence | SHA-256 |
|---|---|
| Fixed CNF source | `5e2d1b46b2cfc793141155b93a83ed423bfd2a9fb588b19d540b933a5fe07061` |
| Reusable CNF object | `92da4241b89da151d9f3560cfa68c7c1338578c291bd677f48d429a94a7bd5fa` |
| CNF stable receipt | `f6713d0f75b00fd41fc4c16f8909180cb3be53df6d3dba499e1b512e85cd349e` |
| `lean/CoreSemantics129.lean` | `9d09552f1f832f2606fec8b0a88fad4d532321219269c4474388db5ca9d67310` |
| `audit/generate_core_semantics.py` | `91da3beb57d5ed6f143d2c86479d5c60053a33e031e08bad332e5b968ab1d64f` |
| `audit/core-semantics-generation.json` | `4a98eb4e99f6bb284bed5145642d537ca8f1fd19ee0bd162bc14ed967968ac1b` |
| `audit/check_core_semantics.py` | `57797db7ffc01247e6858ff448fbd6499312987434b2ab7edcd0c57f2e1f767f` |
| Reusable semantic object | `9f09c01059965fdc43a50e7f70dc1c89b86f4963accda570b5321bb240d01ca2` |
| Semantic compiler log | `92250fd5e4a8a1b9df403dec1f8dd05179c143b010d4f3673ea8beac8ef6f1a6` |
| Semantic stable receipt | `11f6485613fef7628aca334b41715ea9c2462041136595fa80e39cba8afef5f7` |

The generation record retains its earlier `GENERATED_NOT_YET_CHECKED`
status because those exact bytes are pinned by the successful receipt. The
later successful compiler receipt supplies the checked status. All earlier
checked helper modules remain unchanged, and no additional check is running
for this semantic task.
