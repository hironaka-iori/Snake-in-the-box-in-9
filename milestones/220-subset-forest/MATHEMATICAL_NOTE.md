# Round 220: subset forest bounds and Boolean product consistency

The target remains a 93-edge induced partner to the saved 98-edge Q8 path, beginning at endpoint 0 or 78 and avoiding its other 98 vertices. A compatible partner gives 192 Q9 edges. This round obtains no partner and no new global upper bound.

## Exact result

Subset forest inequalities strengthen the previous continuous model. Adding 25 witnessed inequalities at each root yields these exact bounds on total selection weight:

| Root | Exact feasible weight | Exact upper certificate |
|---|---|---|
| 0 | 22588258102073/230867380070 | 97840921/1000000 = 97.840921 |
| 78 | 3545809907526/36419686519 | 97359759/1000000 = 97.359759 |

The feasible weights are approximately 97.840839 and 97.359704. They satisfy every simple-cycle occupancy inequality and every subset forest inequality, as certified below. Convex mixtures with the one-edge paths [0,2] and [78,14] have total weight exactly 94 and preserve both complete families. Thus this stronger continuous formulation still cannot exclude the 93-edge target.

Both upper bounds are below 98. An actual odd-edge partner has even vertex count, so it has at most 96 vertices and 95 edges. In particular, a 97-edge partner is excluded at either endpoint. Any partner of at least 97 edges would contain such a prefix, so arbitrary partners for this fixed parent have at most 96 edges. A one-crossing join using this parent consequently has at most 195 edges. This recovers the previous native 97-edge exclusions with exact weighted inequalities. It does not cover different parents or other face arrangements.

## Why the subset inequalities hold

Let x be Boolean vertex selection and y the induced-edge product. For every subset U and v in U,

\[
\sum_{ab\in E(U)}y_{ab}\le\sum_{u\in U}x_u-x_v.
\]

The part of a path inside U is a forest. If v is selected, this forest is nonempty and has at most one fewer edge than vertices. Otherwise the weaker bound holds, including for an empty selection.

Forest220 checks the bound directly from an actual indexed induced path. Every selected ambient edge joins consecutive indices. Map each edge to its endpoint farther from a marked selected index. This map is injective and avoids that marked index. The empty case is handled separately. A further checked algebraic implication uses the signed degree-sum identity.

Set endpoint mass eta_t=1 at the root and eta_u=e_u elsewhere. Summing degree equations gives

\[
2\sum_U x-\sum_U\eta=2\sum_{E(U)}y+\sum_{\delta(U)}y.
\]

Therefore the subset inequality is equivalent to

\[
\sum_{\delta(U)}y+\sum_U\eta\ge2x_v.
\]

Give each original edge capacity y and add an edge of capacity eta_u from each vertex to a new sink. A minimum v-to-sink cut identifies a most violated subset containing v. The round-219 points give 22 witnessed violations at root 0 and 23 at root 78, including their weight-94 mixtures. Two additional separation iterations produce 25 saved rows per root.

The saved upper certificates use the exact weighted-row method of round 219. Nonnegative inequality weights, signed equality weights and residual compensation are checked with integers. Numerical optimizer optimality is unnecessary for those upper bounds.

## Exact feasibility of the complete families

The new rational points are checked against every model row and bound. Deleted-edge potentials certify all cycle occupancy inequalities, using the round-219 telescoping argument. For the subset family, each vertex has a separate feasible flow to the new sink with source supply at least twice its selection weight. Summing conservation over any subset containing the source bounds its supply by the cut capacity. This proves every subset inequality, without relying on numerical separation completeness or maximum-flow optimality.

The independent audit checks 574 variable bounds and 1,870 or 1,865 rows, 337 cycle potentials, and 158 feasible flows on 832 directed arcs per root. It verifies all capacities, conservation equations and degree identities. Each flow belongs to a separate certificate; no simultaneous multicommodity flow is asserted.

The exact weight-94 mixtures use weights 21239798966440/22126523341933 and 837652789937/868242633622 on the larger points. Their coordinates, model rows and objective are checked again. The one-edge paths satisfy both complete inequality families, which are preserved by convexity. None of these fractional points specifies a Boolean path.

## A concrete missing condition

For Boolean selections, d_ab=x_a+x_b-2y_ab records whether the endpoint selections differ. Around a closed cycle the number of disagreements is even. Thus, for every odd-sized edge subset F,

\[
\sum_{e\in F}d_e-\sum_{e\in C\setminus F}d_e\le |F|-1.
\]

At least one edge must disagree with the prescribed odd pattern F. These are the classical cut-polytope cycle inequalities of Barahona and Mahjoub, *Mathematical Programming* 36 (1986), 157–173. The author-hosted primary source was inspected: https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM86.pdf. This application and its exact witnesses do not imply a new general inequality.

The root-0 rational point has disagreement values (0,1,0,0) around square (44,45,61,60), violating the singleton-edge inequality by one. Three zero disagreements force all four Boolean selections to agree, contradicting the fourth edge. The weight-94 mixture still violates the inequality by 21239798966440/22126523341933. Root 78 also has explicit square violations.

An independent audit recomputes 20,512 odd-subset inequalities on the saved squares and six-cycles across all four points. The respective violation counts are 85,64,66,51 for root-0 primal, root-0 weight94, root-78 primal and root-78 weight94. Square inequalities alone exclude every saved point. This excludes those points, not all fractional assignments of weight 94.

SquareParity220 checks the Boolean product/disagreement identity and the two square inequality forms. All three reports use no axioms. Rotating the arguments covers the eight odd-subset inequalities on a square. The general-cycle argument is written above. No parity-strengthened LP was solved this round.

## Verification and paper review

Two new Lean modules supply seven accepted results. Forest220 uses only standard foundational axioms; SquareParity220 reports none. Their concrete numerical arrays and graph-to-model interpretation are not assembled into one Lean theorem. The separate native exact audits are preserved with source hashes. The native computations are terminal, with no resource stop. No software tests were created or run.

The full 10,979-line pre-revision manuscript and all 620 frontier lines were read across assigned reviews. Corrections include a historical 235 proof incorrectly referring to the current 233 theorem, a misnamed window summand, ambiguous baseline/count notation and stale search status. Every existing theorem/reference label is retained. The short explanation is consolidated around the current deduction chain. The review does not rebuild archived finite proofs or independently recheck every printed witness. Authors and hyperlink settings are preserved; final compilation receipts and exact mirror verification accompany publication.

## Next step and maintained scope

Add all eight square parity inequalities on every allowed coordinate square, keeping the existing degree, edge-product, occupancy and subset rows. Reoptimize both roots, separate any newly violated subset constraints, and audit an exact upper certificate. If the bound still exceeds 94, reconstruct an exact feasible point and check the complete families before claiming another barrier. Longer cut-parity cycles can be separated by the classical two-copy shortest-path construction; the initial priority is the already justified square family. Do not infer infeasibility from removal of the present points.

The maintained global interval remains 191<=a(9)<=233, with the contributor's complete saved theorem and the independent full rebuild still distinct. The 196 conjecture remains unresolved. Earlier parent searches are unchanged, with only one of 28 six-coordinate cases exhausted. The goal remains ACTIVE. Contributor work has not triggered a pause. No email is sent because no sending connection is available. The next scheduled full-paper review is round 230.
