# Round 219: exact fractional points and all-cycle certificates

Both rational points and both exact-cardinality-94 mixtures passed independent exact arithmetic. Each fixed-root continuous edge model remains feasible with 94 selected vertices after every simple-cycle occupancy inequality is imposed. Consequently this family of continuous constraints cannot exclude the requested cardinality. This conclusion concerns the relaxation; neither point is a Boolean partner path.

The baseline audit is unchanged. The present audit checked its hash, all referenced source pins, and the exact model hashes before using the previously reconstructed integer rows.

## Rational feasibility

For each root, all 574 rational coordinates lie in the saved interval from 0 to 1. Every saved row was evaluated with exact rational arithmetic: 1,845 rows for root 0 and 1,840 for root 78. Objective coefficients, certificate hashes, producer-source hashes, and recorded summaries agree.

| Root | Exact feasible objective | Approximate value | Nonintegral coordinates |
|---:|---:|---:|---:|
| 0 | \(43286778654/441499285\) | \(98.0449575451\) | 405 |
| 78 | \(75253867064343/770614508036\) | \(97.6543606169\) | 405 |

Both objectives exceed 94 and lie below the independently certified upper bounds. The exact upper-minus-primal gaps are respectively

\[
\frac{3022280641}{44149928500000},\qquad
\frac{859513625243}{12040851688062500}.
\]

These positive gaps do not certify exact optimality. The numerical basis was used by the producer to obtain the points; this audit checks their coordinates directly and does not rely on basis status, numerical optimality, or repeating the elimination.

## Every simple-cycle inequality

Put \(c_v=1-x_v\). For each of the 337 graph edges \(st\), the certificate supplies a rational potential \(p\) on all 158 vertices. Independently checked conditions are

\[
p(s)=0,\qquad
|p(u)-p(v)|\le c_u+c_v
\quad\text{for every edge }uv\ne st,
\]

and

\[
p(t)+c_s+c_t\ge2.
\]

This gives 113,232 checked edge inequalities per root. The potential list contains every graph edge exactly once, in the saved order. An independent traversal of each edge-deleted graph confirms that every corresponding target is reachable.

For any simple cycle \(C\), choose an edge \(st\) on it. Telescoping along the complementary path gives

\[
p(t)\le 2\sum_{v\in C}c_v-c_s-c_t.
\]

Combining the two inequalities proves \(\sum_{v\in C}c_v\ge1\), equivalently \(\sum_{v\in C}x_v\le |C|-1\). This argument covers all simple cycles, including cycles with chords. It requires no exact shortest-path assertion.

The lower bound is attained: the saved square on vertices \(\{102,110,118,126\}\) has cost exactly 1 for root 0, and the square \(\{4,6,20,22\}\) has cost exactly 1 for root 78. Thus the minimum cost over actual simple cycles is exactly 1, independently of floating-tolerance separation.

## Exact target cardinality

The second certificate for each root combines the preceding point with the actual one-edge path \([0,2]\) or \([78,14]\). The short path's complete 574-variable encoding was independently reconstructed: its two selected vertices, its odd endpoint, and its selected edge have value 1, with all other coordinates 0. Both encodings satisfy every saved row and variable bound exactly.

Writing \(Q\) for the corresponding objective in the table, the mixing weight is \(92/(Q-2)\). The checked weights are

\[
\frac{10154483555}{10600945021}
\quad\text{and}\quad
\frac{70896534739312}{73712638048271},
\]

both strictly between 0 and 1. Every mixed coordinate was recomputed from the two endpoints. Every row and bound was checked again, and each mixed objective is exactly 94. The mixtures have 416 and 422 nonintegral coordinates, respectively.

All simple-cycle occupancy inequalities are linear. The original points satisfy them by the potential argument; the one-edge paths satisfy them because they select at most two vertices of any simple cycle. Therefore the mixtures satisfy every such inequality as well. The target-cardinality equality does not remove these fractional feasible points.

## Evidence and limitations

The accepted rational reconstruction execution reports exit 0, no stop, 3.796 seconds, maximum sampled private memory 46,342,144 bytes, and minimum sampled free memory 1,052,721,152 bytes. Its source/input pins, stdout/stderr hashes, summary hash, thread limits, and resource samples match. These are sampled resource observations.

Only saved-record reading and exact arithmetic were run for this audit. No solver, proof compiler, search worker, basis reconstruction, or software tests were invoked. The certificate argument is written and checked by native exact arithmetic; this audit makes no claim that its entire finite verification has been accepted by Lean. Integrality, connectivity, other valid inequalities, and alternate constructions remain outside the limitation established here. No global snake bound follows.

## Source pins

- `scripts/audit_rational.py`: `a540aa7e07d1156a51bae0570ca7b49acd158cd8d81cd4c1e4c39492f16af05f`
- `scripts/rational_basis.py`: `cbd410b689f4e812cc9ba4ca88e50b7c292de78b9ded710ddb66e625f3c1514b`
- `scripts/run_rational.py`: `7926120d76b06346c1131610451c473ca587a46cd0d435ab36034a3ff5379c64`
- `scripts/target_point.py`: `e2ea948b3c82a6c77eae80107b6684c102f37d82f8e0e75d6465f4b551c82fc6`
- Frozen baseline `data/linear-audit.json`: `b408c13775470f5bf903db4bdd52aa5d3444b0d7268847ff728018eaf5e11d37`

All model, basis, primal, target-cardinality, execution, and summary hashes are recorded in `data/rational-audit.json`. The producer certificates and the baseline audit files were not altered.
