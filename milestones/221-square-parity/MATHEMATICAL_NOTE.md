# Round 221: cycle parity and exact partner bounds

The saved 98-edge Q8 parent has no compatible 95-edge partner beginning at either endpoint. Exact weighted certificates now limit its one-crossing construction to 193 edges. The 93-edge partner needed for a 192-edge Q9 snake remains unresolved. Three of fourteen possible first-step branches are excluded.

This is a restriction on one parent and one joining arrangement. The maintained global interval remains \(191\le a(9)\le233\); the independent full rebuild of the contributor's saved233 assembly remains pending. No new snake or global bound is claimed.

## Model and hypothesis

For root \(t\in\{0,78\}\), remove all other vertices of the saved parent. Each allowed graph has 158 vertices and 337 edges. The partner's other endpoint is free. The model uses vertex selections \(x\), opposite endpoint selections \(e\), and induced-edge variables \(y\). It retains the previous degree equations, parity balance, linear product inequalities, occupancy-cycle inequalities and subset forest inequalities. An actual odd-edge partner satisfies every row. A 93-edge target selects 94 vertices.

The round began with the hypothesis that adding Boolean consistency of the products could reduce the exact upper bound, while recognizing that removing known fractional examples need not remove all target-size points. The computation supports the first claim and refutes the stronger expectation that these complete cycle families alone exclude 94.

## Why the new rows are valid

For Boolean selections and \(y_{uv}=x_ux_v\), put \(d_{uv}=x_u+x_v-2y_{uv}\). This is the indicator that the endpoint selections differ. A closed walk has an even number of disagreements. For an odd marked edge subset \(F\), the disagreement pattern differs from the marking somewhere. Therefore

\[
\sum_{e\in F}d_e-\sum_{e\notin F}d_e\le |F|-1.
\]

Indeed, the left side is \(|F|\) minus the number of mismatches. The new Lean module `CutParity221` derives even parity from explicit walk closure, then proves this general inequality. Both exported results passed on the first attempt, with only standard foundation axioms. The earlier Boolean product identity and square forms remain in `SquareParity220`. Concrete cycle lists and coefficient assembly have independent integer audits and remain separate from a complete Lean assembly.

These are classical cut-polytope cycle inequalities, not a novelty claim. The two-copy method follows the primary source [Barahona and Mahjoub, On the cut polytope (1986)](https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM86.pdf), inspected in round220.

## Exact upper bounds

All eight odd-subset rows were added on each coordinate square: 156 squares at root0 and154 at root78. The resulting bounds are96.000722 and95.779317. Exact rational points expose further violated cycles of lengths6 through14. A second stage adds27 longer parity rows at root0 and8 at root78, plus one more forest row at root78.

| Root | Exact final feasible objective | Exact final upper bound |
|---:|---:|---:|
| 0 | \(2507137819890885477/26128236866583647\) | 95.955197 |
| 78 | \(388107824092577/4052758842992\) | 95.763979 |

For scale \(D=10^6\), row vectors \(a_i\), right sides \(b_i\), objective \(c\), and integer weights \(w_i\), the certificates store

\[
r=Dc-\sum_i w_i a_i,
\qquad
Dc\cdot z\le\sum_i w_i b_i+\sum_j\max(r_j,0).
\]

Inequality weights are nonnegative; equality weights may be signed. The residual estimate follows from \(0\le z_j\le1\). Independent audits reconstruct all added rows and every residual coordinate. The deduction does not require numerical optimality.

A95-edge partner would have96vertices, contradicting either bound. Every longer compatible partner contains such a prefix. Thus arbitrary compatible partners at these roots have at most94edges, and this one-crossing join has at most \(98+94+1=193\) edges. Other parents and arrangements remain outside this result.

## Why every inequality in all three families still permits 94

The final exact rational points satisfy more than their finite row lists.

1. **Occupancy cycles.** Put \(c_u=1-x_u\). For each removed edge \(st\), a potential with \(p_s=0\), \(|p_u-p_v|\le c_u+c_v\) on remaining edges, and \(p_t+c_s+c_t\ge2\) proves \(\sum_{u\in C}c_u\ge1\) for every cycle containing that edge. There are337 potential systems per root.
2. **All subset forest rows.** Each original edge has capacity \(y_{uv}\), and vertices have sink capacity1 at the root and \(e_u\) elsewhere. For each vertex \(v\), a feasible flow sends at least \(2x_v\) to the sink. Conservation over any subset \(U\) containing \(v\) gives boundary capacity plus endpoint mass at least \(2x_v\). Summing the degree identities over \(U\) converts this to \(\sum_{E(U)}y\le\sum_Ux-x_v\). All158 flows per root are saved and checked with arbitrary integers.
3. **All disagreement-cycle parity rows.** Double each graph vertex. An edge has cost \(d_{uv}\) when preserving the copy label and \(1-d_{uv}\) when switching it. For each original vertex, a saved potential is0 at its first copy and at least1 at its second, with \(p(b)-p(a)\le c_{ab}\) on every directed arc. An odd-marked cycle lifts to a walk between those copies. Telescoping proves \(\sum_F(1-d_e)+\sum_{C\setminus F}d_e\ge1\), the required parity inequality. All158 potentials per root are saved.

These are feasible potential and flow certificates. No shortest-path or maximum-flow optimality assumption enters these implications. The independent audit verifies113,232 occupancy edge inequalities,131,456 flow-capacity inequalities,158 degree identities and425,968 two-copy arc inequalities per root.

Both objectives \(q\) exceed94. Mixing with the actual one-edge path using weight \(92/(q-2)\) gives exact objective94. Linearity preserves every inequality in all three complete families. The mixtures are independently audited. They remain fractional and do not provide a path. Root0 flow capacities require arbitrary integers: total arc capacity is60,171,307,677,381,251,448, exceeding signed64-bit capacity.

## First-step disjunction

Every actual partner chooses one first neighbour. The allowed choices, obtained independently by flipping each of eight bits, are

\[
N(0)=\{2,4,8,16,32,64,128\},\qquad
N(78)=\{14,74,76,79,94,110,206\}.
\]

For each branch add \(x_w=1\). The root's neighbour sum is1, so the other choices are zero. These cases cover every actual path; fractional points can distribute their first-step weight and need not belong to a branch.

| Root | First vertex | Exact upper bound |93-edge target |
|---:|---:|---:|---|
|0|2|94.488969|Unresolved|
|0|4|94.613095|Unresolved|
|0|8|94.558772|Unresolved|
|0|16|92.569610|Excluded|
|0|32|95.018845|Unresolved|
|0|64|95.680069|Unresolved|
|0|128|94.188343|Unresolved|
|78|14|93.517327|Excluded|
|78|74|93.927558|Excluded|
|78|76|94.463971|Unresolved|
|78|79|94.406607|Unresolved|
|78|94|94.229213|Unresolved|
|78|110|94.892792|Unresolved|
|78|206|94.951566|Unresolved|

Exactly three bounds are below94. The other eleven give neither a completion nor exact fractional feasibility evidence. All fourteen sparse weighted certificates, neighbour coverage, terminal execution records and hashes pass an independent audit.

## Evidence and next step

The audit chain is `square-audit.json`, `rational-audit.json`, `long-audit.json`, `long-primal-audit.json` and `first-audit.json`. Final complete-family claims use the long-model primal audit; the earlier square-model primal audit covers only saved rows and occupancy cycles. This distinction prevents an intermediate certificate from being assigned a stronger scope than it has.

Extend the eleven remaining first steps to induced prefixes. Each nonterminal prefix partitions into possible next vertices. Require every prefix vertex to be selected, exclude repeats and chords when enumerating children, and retain an exhaustive ledger. A bound below94 removes that entire prefix region. An unresolved upper bound, solver failure or timeout leaves the region pending. Finite inherited rows already justify an upper certificate; additional cycle separation is optional strengthening.

Goal ACTIVE. This round produced useful progress and does not meet the user-authorized pause conditions of an exceptional result or prolonged stagnation. Contributor changes alone cannot trigger a pause. No email was sent; no email-sending connection is available. Historical parent-search states remain frozen. Both manuscripts were updated in place and successfully compiled, frontier first and main last. Authors and hyperlink settings are preserved. No software tests were created or run. Next full-paper review remains round230.
