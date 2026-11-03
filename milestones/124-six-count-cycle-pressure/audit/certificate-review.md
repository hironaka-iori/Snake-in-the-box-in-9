# Certificate audit for the six-count total on 0123041

The saved certificate passes the exact formula, multiplicity, core, ordered-RUP,
renumbering, semantic-data and source-port checks. This audit concerns the
single direction shape $0123041$ and total cap 24. It establishes no universal
six-count floor.

The canonical window is $(0,1,3,7,15,14,30,28)$. Its six internal centres have
bounds $[0,21]$. The encoding uses all 512 vertices of $Q_9$, 5,072 variables,
and 101,898 clauses. The auditor rebuilt this complete formula and compared
every clause with the saved certificate input. No cycle cuts were appended.

Each internal centre contributes 21 corner occurrences. Across the six
centres, 85 corners occur once, 19 occur twice, and one occurs three times:

$$
85+2\cdot19+3\cdot1=126,
\qquad 85+19+1=105.
$$

The sum counter retains all 126 occurrences. The semantic source's selected
centres, counter literals, meaning tree, tags and permutation statement were
checked against this multiset. Deduplicating to 105 literals would change the
quantity being bounded; that change has not occurred.

The core contains 3,649 original input clauses. Every trimmed proof row matches
its original row byte for byte. All dependencies are available before use,
the input references equal the saved core, and the deductions form the exact
backward dependency closure of the final empty clause, whose ID is 116331.
The audit independently replayed all 5,746 ordered-RUP deductions with 439,766
hints and verified the final contradiction.

The renumbering moves exactly 2,021 active variables to the initial interval.
Every renamed clause and deduction matches the original under that bijection.
The exported raw CNF and semantic metadata also match. All 40 generated modules
were compared with their isolated copies; their changes are restricted to
import prefixes. The auditor decoded every packed deduction in all 72 source
segments and checked its literals, hint order, slot contents and slot reuse
against the renamed LRAT proof. Per-segment hint counts match the export plan.

The selected checker uses 13-bit words, literal offset 2,400 and 3,852 slots.
The active-variable maximum is $2021<2400$; all emitted keys and literal words
fit their representation. The hint count is below the authorized two-million
limit. The exact checker object and the generator, certificate, probe, solver
record, complete formula, core, proof and published sources are pinned.

The export plan records a successful native simulation. Both export attempt
records nevertheless have status `STOPPED`. The first encountered a text-
encoding error. The second saved the complete plan and its hash before an
`OSError(22, 'Invalid argument')`, consistent with failure of the final print
after the plan was saved. It is not recorded as a clean process success.
Neither failure changed the certificate: its SHA256 is
`07aff88bdf4e2bbded77b2efdb6517a8e61babdbb692438f8bef83af197f546f`.
This audit uses the independently validated published plan and sources. Both
failed scratch directories were preserved in archives recorded by
`data/failed-export-archives.json`; the original attempt statuses remain intact.

No solver or Lean compiler was started by the auditor. This saved certificate
audit is distinct from the subsequent review of Lean receipts and the theorem
for actual snakes. The latter must connect the concrete semantic theorem,
core contradiction and actual-window transfer. The remaining direction shapes
and any universal floor of 25 or 26 remain outside this certificate's scope.

Evidence: `data/certificate-audit.json`, SHA256
`8000f83197ae0ffe36c40f4448334af2ce4dc9339ad99197bc60f4ed376f4cf2`.
The repeatable auditor is `scripts/audit_certificate.py`; it writes a new
evidence file exclusively when `--output` is supplied.
