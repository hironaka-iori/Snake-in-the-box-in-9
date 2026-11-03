# Independent review of the endpoint-query core

Result: `PASS_ORIGINAL_CORE_NATIVE_REPLAY_AND_GEOMETRY_REVIEW`. The complete 96,552-clause input, its 2,426 variable meanings, both counters, and all 683 selected original clauses were reconstructed. Tagged and untagged encoders agree exactly. A separate propagation implementation replayed all 13,299 trimmed deductions and 554,859 hints from the selected original clauses, preserving their original IDs, and reached the empty clause. Every selected original clause was referenced. No solver or Lean compiler was run.

The reviewed geometric consequence is: for an induced path in \(Q_9\) with a fitting canonical \(012032\) window, a sum of the second and fourth internal counts at most 9 forces one actual path endpoint to be at Hamming distance 2 from both corresponding centres. No parity hypothesis is needed by this particular certificate. Its conversion to a checked Lean theorem remains a separate task.

## Exact premises

| Clause family | Number in core | Meaning |
| --- | ---: | --- |
| Window units | 7 | The seven displayed vertices are selected. |
| `deg2` | 192 | A selected vertex cannot have three selected neighbours. |
| `lowEnd` | 32 | A selected degree-one vertex has its endpoint flag. |
| `cut` | 10 | These specific six-vertex cycles cannot all be selected. |
| Pair-counter clauses | 435 | The 42 absent-corner occurrences sum to at most 9. |
| Negative endpoint units | 7 | No endpoint occurs at these seven common-sphere vertices. |

The pair-counter families are `first`: 13, `mono`: 219, `step`: 189, and `over`: 14. Every such tag refers to counter index 1. The core contains no clauses from counter 0, which is the global endpoint-count counter. It also contains no positive endpoint-parity clause, `degPos`, `endSel`, `endLow`, counter `zero` clause, or four-cycle exclusion. The ten selected cuts were independently checked to contain six distinct vertices, each with exactly two neighbours inside that set.

Every selected original ID, literal list and tag is saved in `data/endpoint-core-review.json`. This includes the exact mapping for the 435 counter clauses; no clause order or repeated literal occurrence was discarded. These dependencies describe this certificate and do not assert that its core is minimal.

## Counter multiplicity and variable meanings

The normalized window is

\[
(0,1,3,7,6,14,10),
\]

and the two centres are 3 and 6. Each has 21 allowed opposite corners after excluding its two path directions. The two lists contain 42 occurrences over 37 distinct vertices. Vertices

\[
18,34,66,130,258
\]

occur once in each list and must each be counted twice in the pair sum. Replacing the concatenation by a set would change the mathematical condition. The independent checker rebuilt every pair-counter clause directly from the occurrence list and the sequential-register indices.

Primary variable \(v+1\) represents selection of vertex \(v\); variable \(513+v\) is its endpoint flag. A counter register represents a threshold on the number of true literal occurrences in a prefix, including repeated occurrences. The saved variable-meaning and counter tables match the reconstruction exactly. The counter schemas were also checked over all relevant predecessor counts and both possible next-literal truth values.

## Seven used endpoint units

The fourteen vertices at Hamming distance 2 from both centres split as follows:

- Used negative endpoint units: \(0,10,18,34,66,130,258\), at original clause IDs 96539, 96541, 96543, 96545, 96547, 96549 and 96551.
- Unused common-sphere vertices: \(5,15,23,39,71,135,263\).

Each unused vertex is adjacent to the internal window vertex 7. Its two path neighbours, 3 and 6, are already selected and distinct. Selecting any unused vertex would give 7 three selected neighbours, contradicting the induced-path degree condition. Therefore none can be a selected path endpoint. This argument uses no endpoint parity.

Under the negation of the proposed conclusion, both actual endpoints avoid the common sphere, so in particular the seven used endpoint flags are false. The core then gives a contradiction. The proof needs neither of the two positive parity clauses at IDs 96537 and 96538. Although the original search was prepared for odd-length counterexamples, the reduced certificate's assumptions support the conclusion for every path length admitting the six-transition window.

## Remaining Lean and semantic obligations

1. Check the exported refutation in the Lean kernel. The original active variable IDs reach beyond the existing checker's offset, so the exporter is preparing an explicit active-first renaming. Its bijection, literal transport, original clause-ID mapping and transported variable meanings must be checked. This review concerns the original IDs and does not certify an unfinished export.
2. Assign primary variables to actual path membership and endpoint flags to the two actual endpoints. Prove the selected window, degree, degree-one and six-cycle clauses for this assignment. The fitting window implies path length at least 6, so the isolated one-vertex case does not arise.
3. Identify the two internal counts with the two 21-corner absence counts. Transport the sum bound to the concatenated 42-occurrence counter, preserving shared corners twice. Give each register its prefix-occurrence threshold meaning and prove all selected counter clauses.
4. Derive the seven negative endpoint units from failure of the same-endpoint conclusion. The quantifier must say that one endpoint is distance 2 from both centres; allowing a different endpoint for each centre would change the statement.
5. Normalize an arbitrary fitting canonical window by a cube translation and coordinate permutation, preserving actual endpoint identities, path membership, counts and both Hamming distances. Reversal, if included in a later shape convention, requires its own explicit transport.
6. Combine the semantic assignment with the refutation and expose the actual-snake theorem without an external unsatisfiability premise.

No missing parity premise was found. The intrinsic assumptions are an actual induced path in \(Q_9\), a fitting window, the stated canonical direction order, and the pair-count bound. This review supplies neither an endpoint-occurrence budget nor a new global upper bound.

The audit completed without a failed assertion. No parent evidence, exporter files or frozen milestone131 files were edited.

- `data/endpoint-core-review.json`: SHA256 `173c5f19df6dccb6c4a86cc5386106430236d1080124d014928fd0745e836008`.
- `audit/check_endpoint_core.py`: SHA256 `567e506956382265754b0692c7f1da5a1a623441a087d6a8da5630bdd2d14677`.
