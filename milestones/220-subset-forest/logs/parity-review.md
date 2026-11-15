# Independent parity-inequality audit

## Result

All four saved round-220 rational assignments violate valid cycle disagreement inequalities. This includes both assignments of total selection weight exactly 94. Square inequalities already remove every saved assignment; six-cycle inequalities supply additional violations. This is evidence for a further relaxation strengthening. No strengthened linear program was solved in this audit, and feasibility of other fractional assignments of weight 94 remains unresolved.

The independent calculation is `scripts/audit_parity.py`; its exact receipt is `data/parity-audit.json`. It verifies all forty saved largest witnesses, ten per point, and independently recomputes every odd-edge-subset inequality over the saved coordinate squares and six-cycles.

| Root | Point | Saved squares | Saved six-cycles | Odd subsets checked | Square violations | Six-cycle violations | Total |
|---|---|---:|---:|---:|---:|---:|---:|
| 0 | Rational primal | 156 | 123 | 5184 | 56 | 29 | 85 |
| 0 | Weight 94 | 156 | 123 | 5184 | 49 | 15 | 64 |
| 78 | Rational primal | 154 | 120 | 5072 | 51 | 15 | 66 |
| 78 | Weight 94 | 154 | 120 | 5072 | 44 | 7 | 51 |

The audit evaluates 20512 inequalities in total. In these data, each violating saved cycle has exactly one violated odd-subset inequality. The finite scope is the saved 4- and 6-cycle collection; no claim of enumeration of all simple cycles is made.

## Validity

For Boolean vertex choices and their actual induced-edge products, put

\[
d_{uv}=x_u+x_v-2y_{uv},\qquad y_{uv}=x_ux_v.
\]

Then \(d_{uv}\) is zero when the endpoints agree and one when they differ. Along a closed cycle the number of disagreements is even. For an odd edge subset \(F\subseteq E(C)\), this gives

\[
\sum_{e\in F}d_e-\sum_{e\in E(C)\setminus F}d_e\le |F|-1.
\]

Indeed, if at least one edge in \(F\) has disagreement zero, its first sum is at most \(|F|-1\). If every edge of \(F\) has disagreement one, the even cycle total forces at least one disagreement outside \(F\), giving the same bound. Thus the inequalities preserve every actual induced path, and more generally every Boolean vertex selection with its induced-edge products. Connectivity and forest hypotheses are unnecessary for their validity.

These are classical cut-cycle inequalities, rather than a new inequality family. The parent reviewer consulted the author-hosted [BM86 paper, pages 168–169](https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM86.pdf). This audit supplies the direct elementary argument above; it does not claim an independent rereading of that external source.

## Exact examples

At root 0, take the square in cyclic order \((44,45,61,60)\), with \(F\) containing only edge \(45\text{--}61\). The rational primal has disagreement vector \((0,1,0,0)\), so the left side exceeds its zero right side by exactly one. The weight-94 assignment has vector

\[
\left(0,\frac{21239798966440}{22126523341933},0,0\right),
\]

giving exact violation \(21239798966440/22126523341933\), approximately 0.9599248214.

At root 78, the rational primal's largest violation occurs on \((200,216,248,232)\) with the last three edges in \(F\). It equals

\[
\frac{31275760554}{36419686519}\approx0.8587597408.
\]

For the root-78 weight-94 assignment, the largest violation occurs on \((224,225,241,240)\), with only the closing edge in \(F\). Its disagreement vector is

\[
\left(0,0,\frac{118310297195}{868242633622},
\frac{837652789937}{868242633622}\right),
\]

and its exact violation is \(359671246371/434121316811\), approximately 0.8285039975. These examples are square inequalities covered by the checked Boolean results below.

## Audit independence and preservation

The audit imports no producer helper. It reconstructs the cycle orders from each immutable model's graph, generates odd subsets by combinations rather than bit masks, computes the signed sum as twice the selected-edge sum minus the total, and verifies every saved witness's edges, odd subset, disagreement values, left side, right side and positive excess. It checks that the ten saved excesses equal the ten largest independently recomputed excesses.

Model and rational-certificate hashes match both the diagnostic and the prior exact forest audit. The inherited graph, cycles, objective, variables and original rows match the pinned round-219 base model. The full cube-edge relation on the 158 allowed vertices is checked directly. Every rational point is also checked against all 574 variable bounds and every current model row: 1870 rows at root 0 and 1865 at root 78. The exact primal cardinalities are

\[
\frac{22588258102073}{230867380070}
\quad\text{and}\quad
\frac{3545809907526}{36419686519};
\]

both companion target cardinalities are exactly 94.

The earlier forest audit supplies the separate all-cycle potential and all-subset flow certificate checks. Its receipt is pinned here; those complete potential and flow calculations were not repeated. This audit does not alter any model, rational certificate, diagnostic, manuscript or preceding review log.

## Lean result

`lean/SquareParity220.lean` imports only `Std` and introduces no new definitions. It proves:

- `SquareParity220.boolean_disagreement`: the product expression equals Boolean endpoint disagreement, by four Boolean cases.
- `SquareParity220.square_single_edge`: one square-edge disagreement minus the other three is at most zero, by sixteen Boolean cases.
- `SquareParity220.square_three_edges`: three square-edge disagreements minus the fourth are at most two, by sixteen Boolean cases.

Rotating the vertex arguments covers all eight odd-subset inequalities on a square. This rotation observation and the general-cycle argument are written deductions. The source does not import or certify the saved rational arrays.

The prescribed `prepare_proof.py` and `check_core.py` produced a successful `data/SquareParity220-audit.json` receipt on the first compilation attempt. The compiler used one worker, stack limit 8192, a 60-second timeout and the existing resource gate with its 55-second startup-wait limit. Recorded compiler time was 1.0678294 seconds. All three theorem dependency reports contain no axioms. The preserved attempt folder, source, compiler output, object and dependencies are identified by hashes in that receipt and checked again by the parity audit.

No software tests or native optimizer were run. The maintained global interval is unchanged, and this result establishes no Boolean partner or improved snake construction.
