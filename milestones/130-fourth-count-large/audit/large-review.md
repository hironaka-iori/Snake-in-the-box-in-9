# Independent audit of the fourth-count-at-least-four case

The input audit passed. The resumed native search timed out, so this round
does not exclude the case or prove a new six-count lower bound.

The successful audit completed on 3 November 2026 at 12:21:13 UTC. Its
verification record is `data/large-review.json`. No solver or Lean compiler
was launched by the auditor.

## Exact input and mathematical scope

The input retains all 104529 clauses of the milestone 128 paired formula,
with identical clause order and literal order. It appends exactly 717
clauses for one counter. The final formula has 105246 clauses, 9062 declared
variable identifiers and 6605 occurring variables.

The new counter contains the 21 selected-corner literals at the fourth
internal centre of the normalized window

\[
0,1,3,7,6,14,10,26.
\]

That centre is 6, with incident path directions 0 and 3. Independently
enumerating pairs of its seven unused directions gives the corner list

\[
0,20,36,68,132,260,18,34,66,130,258,
54,86,150,278,102,166,294,198,326,390.
\]

All 21 corners are distinct. Their primary variable identifiers are their
vertex values plus one. The counter limits selected corners to seventeen,
which is the appropriate constraint for at least four absent corners.

The audit reconstructed every clause, tag and register meaning without
importing the producer's encoding or counter helper. It checked:

- Counter index 9 and selected-occurrence upper limit 17.
- Exactly 357 fresh register variables, with identifiers 8706 through 9062.
- Disjointness from all preceding variable identifiers.
- Exact equality of the saved counter data and reconstructed data.
- Exact serialization of the appended clauses and the complete input.
- 446 local prefix-threshold cases and 15574 clause evaluations for the
  intended register assignment.

The reconstructed clause families have sizes 21 first clauses, sixteen
initial-zero clauses, 340 monotonicity clauses, 320 step clauses and twenty
overflow clauses. Their sum is 717.

The original necessary intervals are
\([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]\). The complementary case
raises only the fourth lower endpoint to four. The previous pair inequality
remains in the unchanged base. No additional first-count lower bound three,
second-count lower bound five, or other-three upper bound eleven is appended.
Those constraints belonged to the fourth-count-equals-three case.

The checked `actual_large_bounds` theorem has the matching fitting-window,
canonical-word, six-total-at-most-22 and fourth-count-at-least-four hypotheses.
Its current source, source snapshot, checker snapshot, successful receipt,
objects, compiler log and dependency pins match. All five axiom reports in
that module use only `propext`, `Classical.choice` and `Quot.sound`.

This audit establishes the exact encoding and its relation to the stated
necessary conditions. The separate Lean interpretation of the concrete
added clauses is recorded in its own module receipts. Complete transfer of
the combined input and a contradiction remain separate requirements.

## Interrupted first search

The first search record still contains the historical status `RUNNING`.
The auditor independently found neither its driver PID 15392 nor its solver
PID 47988. No exit code or timeout is inferred from that stale record.

The preserved trace has 52822016 bytes. Its textual scan finds 105479 records,
including 91468 deduction-like records and 14011 deletion records. It has no
empty-clause record and ends in an unterminated record without the final zero.
These scan counts are not counts of verified deductions.

The first 5000 deductions passed ordered positive-RUP replay against the
exact 105246-clause input, processing 277807 hints and 2508 deletion records.
There is no empty clause in that checked prefix. The remaining trace was not
replayed. The preserved partial file therefore supplies no contradiction.

## Resumed search

The separately recorded resumed run ended with `TIMEOUT` after 300.172 wall
seconds. Its recorded process CPU time is 29.546875 seconds, comprising
7.140625 kernel seconds and 22.40625 user seconds. Both standard output and
standard error are empty. The process exit code recorded after termination
is one, not a SAT or UNSAT success code.

The resumed trace has 220307456 bytes. Its first 5000 deductions also passed
ordered positive-RUP replay, with 277807 hints. The consumed prefix hash is
identical to the checked prefix of the first trace. This is consistent with
the unchanged input and seed; it does not establish the later deductions.

A separate complete textual scan, saved in `data/large-resumed-scan.json`,
finds 338116 records: 281345 deduction-like records and 56771 deletion records.
It finds no empty-clause record. The final record is unterminated and lacks
the closing zero. This scan does not replay the deductions after the checked
prefix. There is no complete refutation or model to report.

## Reproducibility and limits

The auditor reuses the previously independent positive-RUP reader and local
counter reconstruction from milestone 129 as copied source. It imports no
producer encoding or proof-checking helper. All source and evidence hashes
are pinned in the JSON record and rechecked at the end of the audit.

Two earlier audit attempts completed the input checks but stopped at the
replay memory gate, with 638214144 and 899350528 bytes available. Their
observations and the exact earlier auditor source are preserved. The final
successful run passed the same replay gate and did not require a resource
wait. No proof result is attributed to the two deferred attempts.

| Evidence | SHA256 |
|---|---|
| `audit/audit_large.py` | `93649960019208f6d47553324db04d91ec4efdc7f75ce1a45e30bd5fed0fc643` |
| `data/large-review.json` | `d7b19dc090fce64b7254ac5b8af9bec573482c31d7e3411d027bf06a3e6d3f68` |
| `work/large.cnf` | `85ed4f2dc93e3ce81f4b347ba2a399ad6034afc019cc06fa253e8d792b6ac67a` |
| Original interrupted trace | `276b386bd59ce1703dbe605959a6e4a6977f7da6e953df7519375e395f355388` |
| Resumed timeout trace | `36213dc1ddcebdb61b10c8a709215e4573b8b287e5a63c3b27df3fa89a021a08` |

The case \(\alpha_{r+4}\ge4\) under the six-count cap 22 remains unresolved.
Neither an exclusion of this case nor a new global upper bound follows from
the audited input, the timeout, or the two valid proof prefixes.
