# Window encoding audit and semantic map

Status: complete Lean semantic bridge, both exclusions and global 244 passed the final source-only audit.
Neither this document nor a refutation of the Boolean formula proves a geometric
exclusion by itself. Base: main commit 537513d; Lean 4.19.0.

## Parameters and necessary hypotheses

The model takes a five-vertex induced path window, a radius, and three target
singleton-square counts. For the present certificates the windows are
`[0,1,3,7,6]` and `[0,1,3,7,15]`, radius 3, counts `[2,2,3]`.
The ball is the union of the three centre balls. A selected vertex means a
vertex on the **whole** snake, not merely on the five-vertex window.
The snake must contain the window and therefore have at least four edges.
This hypothesis is needed by the positive-degree clauses: those clauses would
not be valid for a zero-edge snake considered without a window.

## Variables

| Name | Semantic value | Number in either instance |
| --- | --- | ---: |
| `x{v}` (ID `v+1`) | `v` belongs to the snake | 221 |
| `end{v}` | `v` is selected and has at most one selected neighbour | 95 |
| `prefix{i}_j`, j=1,2 | at least j of the first i+1 endpoint variables are true | 190 |
| `missing{c}_{i}_{j}` | at least j absent opposite corners among the first i eligible axis pairs at centre c | 210 |

Unused vertex IDs below 513 can be assigned false. All auxiliary IDs are
allocated consecutively starting at 513. Endpoint variables exist precisely
where all nine neighbours lie in the ball. Counter variables have a specified
semantic assignment even when their CNF only constrains one direction.
The missing-counter boundary constants are count-at-least-zero = true and
positive thresholds on an empty prefix = false.

## Clause families

Here X is selection, E endpoint status, P a prefix threshold; A/B/C/S are
the four inputs of a counter recurrence, and ¬ denotes a negative literal.

| Family | Clauses | Geometric or arithmetic reason |
| --- | --- | --- |
| window_selected | X(v) | the five window vertices are on the snake |
| degree_at_most_two | ¬X(v) ∨ ¬X(a) ∨ ¬X(b) ∨ ¬X(c) | three distinct selected neighbours contradict path degree ≤2 |
| interior_positive_degree | ¬X(v) ∨ disjunction of all nine neighbours | a selected vertex of a nontrivial path has a selected neighbour |
| endpoint_selected | ¬E(v) ∨ X(v) | definition of E |
| degree_one_implies_endpoint | ¬X(v) ∨ E(v) ∨ all neighbours except one | without any of the other neighbours, degree is at most one |
| endpoint_degree_at_most_one | ¬E(v) ∨ ¬X(a) ∨ ¬X(b) | a and b are distinct neighbours |
| counter_current | ¬E(i) ∨ P(i,1) | a true current entry contributes one |
| counter_carry_one | ¬P(i-1,1) ∨ P(i,1) | counts do not decrease |
| counter_carry_two | ¬P(i-1,2) ∨ P(i,2) | counts do not decrease |
| counter_increment | ¬E(i) ∨ ¬P(i-1,1) ∨ P(i,2) | adding a true entry increases the count |
| counter_overflow | ¬E(i) ∨ ¬P(i-1,2) | a path has at most two endpoints; the vertex list has no duplicates |
| missing_counter | ¬A∨S; ¬B∨¬C∨S; ¬S∨A∨B; ¬S∨A∨C | S ↔ A∨(B∧C), with B = absent current corner |
| missing_exact_lower | final threshold k | exactly k singleton squares implies at least k absent eligible corners |
| missing_exact_upper | negated final threshold k+1 | exactly k singleton squares implies fewer than k+1 absent eligible corners |
| cycle | disjunction of ¬X(v), v in the recorded set | every member has two distinct neighbours inside this nonempty finite set; such a set cannot lie in a path |

The first three transition coordinates are distinct. The fourth can repeat
the first or be new; it cannot repeat the second or third. This is why both
window shapes must be covered, without assuming the alpha-2-specific repeated
window exclusion used in the existing (2,2,2) proof.

At each centre the two window neighbours saturate its available degree. The
other seven coordinate neighbours are absent. A singleton square cannot use
either of the two window directions. Among the remaining 21 axis pairs, it is
a singleton precisely when the opposite corner is absent. Proving this equality
with `SquareIncidence.localAlpha` is proved by `WindowAlpha.localAlpha_corner_list`.
`WindowNormalization.normalize_five_to_standard` preserves these counts under
normalization. Both, all concrete instances and the final source-only audit have passed.

Boolean constants, repeated literals and tautologies are simplified by the
encoder. Their simplification must be accounted for in the Lean instantiation;
the encoder is not trusted. A core only deletes clauses, so satisfying the full
encoding implies satisfying its core. Core indices are checked against the
full generated formula by the executable audit and must also be linked to the
Lean family proofs.

## Checked data and discrepancies from the task description

`audit_encoding.py` regenerates both compact encodings, compares DIMACS and
JSON, checks core mappings, validates all cycle sets, replays the original
LRAT, and independently unit-propagates every retained RUP step.

| Shape | Full clauses | Original LRAT steps | Core clauses | Core RUP steps |
| --- | ---: | ---: | ---: | ---: |
| repeated | 15,235 | 3,744 | 1,588 | 2,327 |
| distinct | 15,242 | 24,895 | 2,728 | 18,461 |

The 3,744/24,895 figures in the task are original LRAT counts, not the trimmed
core counts. Per-family counts and input SHA256s are in
`outputs/window244/encoding-audit.json`. No new solver invocation was made by
this audit. Replay is executable evidence, not kernel verification.

## Kernel progress

`WindowGeometry.lean` proves generic cycle exclusion, endpoint-count ≤2,
positive-degree neighbour existence, missing-threshold recurrence and its four
clause templates. The final chain was reconstructed from source, including every custom foundation dependency.

`check_certificates.py` independently compiles split RUP proof sources and
records source/import/object hashes. Success is explicitly named
`PASSED_BOOLEAN_ONLY`. It monitors private process memory at 0.2-second
intervals against 1,800 MiB; this is an approximate external budget, with
observed peak recorded. Lean 4.19.0 on Windows rejects its advertised `-M`
option as an unknown `max_memory` configuration. The initial monolithic input
module exceeded budget; input structures and input lemmas are now split too.

Completed: parameterized assignment, family-by-family satisfaction, finite
geometry checks, alpha/absent-corner identity, both shapes under normalization,
reversal, both exclusions, global integration, source-only reconstruction and
final transitive axiom audit. The unconditional global upper bound is 244.
Final records are in `outputs/window244/final-verification.json`,
`final-reproduction-manifest.json` and `FinalAudit.log`.
