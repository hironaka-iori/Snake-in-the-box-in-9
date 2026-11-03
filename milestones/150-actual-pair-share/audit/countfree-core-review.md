# Count-free core review for the highpair16 certificate

Status: `PASS_COUNT_FREE_CORE_AND_PROOF_DEPENDENCY_AUDIT`.

The added pair condition is unnecessary for this saved contradiction. All 13,655 retained input clauses belong to the original 92,640-clause count-free 012032 input. Every retained proof variable also belongs to that original input. The certificate therefore supports unsatisfiability of the historical count-free cap 15 Boolean model, without the additional condition that the two centre counts sum to at least 10.

This conclusion uses the existing complete native RUP replay after exact source, input, proof and receipt verification. This review did not run Lean or repeat unit propagation.

## Independent checks

The historical compressed input was decompressed and its SHA256 matched the 72 metadata. Its 92,640 ordered clauses exactly equal the first 92,640 clauses of 150's input. Independently rebuilding `TaggedShare([0,1,2,0,3,2], [(0,21)]*5, 15, M=12)` reproduced that complete historical input.

Reconstructing the additional counter reproduced all 508 appended clauses, all 174 new variables, the complete extended input and its saved meanings. The 42 corner occurrences contain 37 distinct vertices; multiplicity was preserved. No solver object was instantiated.

The core IDs are sorted, unique, range from 1 to 92640, and select exactly the same 13,655 clauses from both inputs, preserving every literal and its position. A structural scan of every trimmed deduction confirmed backward-valid positive references, use of exactly those core IDs, and the final empty clause. It found:

| Item | Verified count |
| --- | ---: |
| Original variables | 11,378 |
| Extended variables | 11,552 |
| Retained core clauses | 13,655 |
| Distinct core variables | 5,442 |
| Distinct derived-clause variables | 4,406 |
| Derived clauses | 58,182 |
| Positive references | 5,350,080 |
| Maximum references in one deduction | 860 |
| Maximum derived-clause length | 81 |
| Added pair clauses used | 0 |
| Added pair variables in core or proof | 0 |

All derived variables are already among the core variables. The final empty clause has original ID 205425. The retained standard cycle clauses comprise 246 four-vertex cuts and 69 six-vertex cuts. There are no additional cycle exclusions. The endpoint budget remains the ordinary limit of two endpoints; no endpoint-location or parity condition was added.

The retained core file still declares 11,552 variables in its header. Variables 11379 through 11552 occur in neither the core nor the trimmed deductions. An unused variable declaration adds no Boolean constraint.

## Replay evidence and scope

The solver worker ended with exit 20 and `s UNSATISFIABLE`; the independent replay worker ended with exit 0. Their output hashes match the saved records, and replay stdout exactly reproduces `native-replay.json`. The saved driver, trimmer and replay implementation match their pinned current source bytes. Input, core, original-ID list, raw proof and trimmed proof hashes all match.

The replay implementation negates each proposed clause, validates its ordered positive references against the core or earlier derived clauses, requires unit/conflict propagation, and inserts the derived clause. References after an established conflict must still name existing clauses. It checks the final empty clause and exact deduction/reference totals. The trimmer drops deletion lines while retaining the positive-reference dependency closure; all references in its output were independently checked here.

The generic replay function does not separately check the original variable upper bound in derived clauses. This review checked that bound for every retained literal, with no violation. No reason requiring a second full RUP replay was found.

## Stronger target and remaining Lean work

The appropriate target now has only the ordinary actual-snake window hypotheses. For any nine-dimensional snake, any valid six-transition window whose canonical directions, in either orientation, are 012032 should satisfy

\[
16 \leq \sum_{i=0}^{4} \operatorname{coreShare}_{12}(p,r+i+1).
\]

The canonical vertex window is `[0,1,3,7,6,14,10]`. All five count bounds are `(0,21)`. No pair minimum, clipped-count condition, length parity or prescribed endpoint position is needed by this certificate. This actual-snake consequence remains pending Lean verification.

Completion requires exact core/variable export, clause interpretation from the ordinary local share axioms, kernel replay of all 58,182 deductions, and composition with the canonical/reversal adapter. The extra pair counter and its 508 clauses should be omitted from that core interpretation. Any graph update or numerical upper bound requires its separate transfer and comparison arguments.

The accompanying JSON records all source and artifact hashes, clause-tag counts and the exact outstanding obligations. The automated reconstruction and structural scan took 1.828 seconds. No active process was touched; no solver, Lean, Git or graph command was run. Only these two review files were written.
