# Review of the six-count certificate and actual-snake consequences

All 46 requested modules passed the receipt audit, with 22 checked axiom
reports and 503 verified files. The result includes a proved six-count floor
of 25 for one direction shape, in either orientation, and conditional upper
bounds for actual snakes. No universal six-count floor or new unconditional
global snake bound has been established.

## Result for one direction shape

For an actual snake with $m$ edges, let a seven-transition window start at
$r$, where $r+7\le m$. If its coordinate-canonical direction word is
$0123041$, in either orientation, the checked theorem gives

$$
25\le\sum_{j=1}^{6}\operatorname{coreAlpha}(p,r+j).
$$

The proof chain is complete for this shape. The generated semantic theorem
turns the local snake conditions and a six-count total at most 24 into a
satisfying assignment of the selected core formula. The compiled LRAT modules
prove that core unsatisfiable. `ActualTotal124.local_refuted` combines the two.
`TotalGeometry124` transfers all six corner counts through an actual canonical
coordinate frame, and `ActualTotal124.actual_total_sum` closes the resulting
actual-snake statement. `Reversal124` applies the statement to the reversed
snake and checks all six reversed indices.

The multiset sum contains 126 corner occurrences and 105 distinct corners.
Repeated corners remain repeated in the semantic counter. The separate
certificate audit rebuilt the full formula, replayed its ordered-RUP proof,
checked the core and renumbering, and decoded every packed source deduction.
The receipt audit confirms that the compiled semantic and contradiction
modules use those exact published source bytes.

## Conditional bounds for actual snakes

`ActualUniform124.count_bounds` derives the two endpoint lower bounds, positive
internal counts and square-count budget for actual snakes. Its proof uses the
existing `GlobalCharge98.core_count_total`, the square-incidence identity and
wedge bound. It does not assume graph charge rules or numerical graph-profile
results.

The following remaining hypotheses are explicit in the checked statements:

| Remaining hypothesis | Consequence for the number $m$ of edges |
| --- | ---: |
| Every internal six-count window has total at least 25 | $m\le234$ |
| Every internal six-count window has total at least 26 | $m\le233$ |
| For $m\ge235$, the total shortfall below 25 across the first 39 disjoint six-count blocks is at most 28 | $m\le234$ |

In the third row, the precise shortfall is

$$
\sum_{b=0}^{38}
\max\left\{0,\,25-\sum_{j=0}^{5}
\operatorname{coreAlpha}(p,6b+j+1)\right\}.
$$

The code uses natural-number subtraction, which is truncated at zero. The 39
blocks cover internal positions 1 through 234, without overlap. Both endpoints
and any remaining internal positions are accounted for separately.

The checked sufficient exception condition is also explicit: if every one of
these block sums is at least 23 and at most 14 block sums are below 25, the
total shortfall is at most $14\cdot2=28$. This suffices for the conditional
bound 234. The earlier 13-block version gives shortfall at most 26 and remains
available. The original source was preserved before the weaker 14-block
condition was added; `data/deficit-refinement.json` pins both versions.

The one-shape theorem does not prove any of the universal floor, minimum-block
sum or exception-count hypotheses above. Establishing an appropriate one of
these hypotheses remains the substantive global task.

## Verification scope

| Module group | Modules | Axiom reports |
| --- | ---: | ---: |
| Exported concrete CNF, semantics and LRAT proof | 40 | 2 |
| `UniformSixBound124` | 1 | 4 |
| `TotalGeometry124` | 1 | 1 |
| `ActualTotal124` | 1 | 5 |
| `Reversal124` | 1 | 2 |
| `SixDeficit124` | 1 | 4 |
| `ActualUniform124` | 1 | 4 |
| Total | 46 | 22 |

For each requested module, the audit checks successful receipt status and exit
code, current source and object hashes, saved source and checker snapshots,
log hashes, dependency pins, printed axiom lists and actual import resolution.
Every reported axiom list is contained in `propext`, `Classical.choice` and
`Quot.sound`. No `sorryAx`, `sorry`, `admit` or `native_decide` appeared in the
checked source/log conditions.

The current `GlobalCharge98` and `CountGeometry` source, object, log and receipt
pins were checked separately, together with their saved count-support evidence.
Their objects are the ones selected by the actual-snake compilation path.
These existing modules are additional dependency checks, outside the 46-module
and 22-report totals.

The first concrete semantic compilation timed out at 180 seconds with an
empty log. Its failed attempt is preserved. The later immutable checker differs
only in increasing the per-module time limit to 600 seconds; it successfully
checked the same semantic source in 386.391 seconds. Each receipt is checked
against its own immutable checker snapshot. The earlier checker and receipt
files were not replaced.

Both export attempt records remain `STOPPED`. The second saved the complete
plan and hash before an `OSError(22, 'Invalid argument')`, consistent with a
failure at the final print. The audit does not reinterpret that process as a
clean success. Both scratch archives are pinned; all 83 files of the final
archive match the published sources, isolated ports, CNF, LRAT and metadata.
The mathematical evidence consists of the validated artifacts and successful
Lean receipts.

This review invokes no solver or compiler. It audits the completed runs and
their exact artifacts. The graph experiment files and all milestone-123 files
remain unchanged.

Evidence: `data/proof-review.json`, SHA256
`b7ebb252f84dfa2ba037b426e16952ba2753404fe0927dc3bc0c7d29298ecbba`.
Certificate evidence: `data/certificate-audit.json`, SHA256
`8000f83197ae0ffe36c40f4448334af2ce4dc9339ad99197bc60f4ed376f4cf2`.
