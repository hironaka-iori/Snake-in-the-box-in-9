# Intervening-count restrictions

This milestone tests the surviving 29-period lower-table cycle from milestone36. At phase18, reversing and normalizing gives directions `(0,1,2,3,4,2,0,3)` and seven singleton counts `(3,4,4,5,5,3,3)`. The two distant counts obey the earlier distance-four inequalities. The intervening counts provide additional restrictions.

## Geometric statements

For distinct coordinates a,b,c,d,e and the eight transitions `(a,b,c,d,e,c,a,d)` starting at position r, suppose the first and seventh internal singleton counts are both at most three. The new statement is

\[
\alpha_{r+3}\ge5,\qquad \alpha_{r+6}\ge5.
\]

The source development supplies arbitrary coordinate normalization and both implications. The completion gate `data/verification.json` passed: both full kernel replays, four refutation/interpretation audits and four normalization/consequence audits use only standard axioms. All 23 saved local forests passed independent checks.

The statements exclude the identified occurrence in the saved cycle. No replacement minimum cycle mean has been certified, and no new global upper bound follows. The paper's interval remains 191 <= a(9) <= 236, using the pinned contributor theorem documented in milestone39.

## Why acyclicity matters

For the first restriction, degree and endpoint clauses alone admit a selected set of 142 vertices with counts `(3,5,4,7,12,10,3)`. It contains three cycles. The saved configuration in `data/cyclic-relaxation.json` passes the independent degree, endpoint, and count checks while failing acyclicity. It is neither a local forest nor a snake.

The ordinary encoding already excludes coordinate squares and the standard induced six-cycles in three-dimensional faces. The first certificate adds 44 further cycle cuts; the second adds four. All four additional cuts in the second case are translates, in the four unused coordinate directions, of the same induced ten-cycle. Every supplied additional cycle and every retained cycle clause has an independent connectivity and degree check; every retained cut is also interpreted by the Lean geometric checker.

| Restriction refuted | Core clauses | Active variables | LRAT hints |
|---|---:|---:|---:|
| First <=3, third <=4, seventh <=3 | 2708 | 1204 | 1141561 |
| First <=3, sixth <=4, seventh <=3 | 1419 | 1029 | 86400 |

The omitted internal counts have their full range 0..21. Positivity is a separate theorem; no extra count hypotheses are hidden in these two statements.

## Positive controls and further hypotheses

Independent local forests attain third count5 with counts `(3,6,5,5,10,11,3)` and sixth count5 with counts `(3,6,10,9,6,5,3)`. They establish the individual thresholds' sharpness in this local model. Extension to full snakes is unresolved. Removing either distant-count hypothesis admits additional local configurations violating the corresponding restriction.

The following stronger observations remain numerical, without Lean joint-counter replays:

- Under the same two distant-count caps, the third and sixth counts have solver lower sum12. A local forest attains12.
- The five intervening counts have solver lower sum24. A local forest attains24.

The value12 does not follow just by adding the two proved lower bounds5. Proving the joint-sum statement requires a separate counter interpretation and replay. The saved cap11 and cap23 refutations provide starting points for that task.

Unconditional triple-sum estimates were also tested. The local model admits counts `(3,10,3,10,10,11,4)`, whose first, third, and seventh counts sum to10, and `(3,6,10,8,6,5,2)`, whose first, sixth, and seventh counts sum to10. These local examples do not refute such inequalities for complete snakes, but show that the current local model cannot prove them without further information.

## Reproduction and scope

Run `scripts/probe.py` and `scripts/extend_probes.py` for the 40 numerical probes. `scripts/certify.py` reuses milestone38's ordinary-core generator and adds the explicitly saved cycle cuts. Run `scripts/replay.ps1 -Case 401`, then case402, then `scripts/check.ps1` for the normalized statements. Run `scripts/archive.py --pack` and `scripts/verify.py` for the final evidence gate.

The scripts reuse the existing Lean4.19 support environment. They do not claim a clean rebuild of all imported support. The independent geometry checker verifies the saved positive configurations, all cycle cuts, core extraction, archive hashes, and the exact saved critical-cycle occurrence. Native solver exclusions outside the two replayed cores retain their numerical status.
