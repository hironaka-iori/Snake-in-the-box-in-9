# Degree-relaxation model review

## Source conclusion

No blocking mathematical or source-level defect was found. The model is a necessary relaxation of every induced 192-edge cube path with exactly two replacements of the specified saved minority class. It permits a path accompanied by disjoint induced cycles. Infeasibility of this larger family therefore excludes the intended path family.

This initial report covers source inspection and preparation of an independent exported-model audit. The new auditor has not been executed by this reviewer. The first four recorded native results are `INFEASIBLE`, each without added cycle cuts; their complete model verification remains pending. The remaining-base worker is owned by the parent.

## Endpoint equation and completeness

For a selected minority vertex the required selected-neighbour count is two. For a selected majority vertex the enforced equation is
\[
\sum_{w\sim v}x_w+e_v=2.
\]
Here \(e_v\) is Boolean, \(e_v\leq x_v\), and the sum of all majority endpoint variables is two. Thus exactly two distinct selected majority vertices have degree one. Every other selected vertex has degree two. The equation is imposed only when the positive selection literal \(x_v\) holds; unselected vertices impose no neighbour-degree condition. This last point is essential and is checked explicitly in every exported model by the prepared auditor.

Every 193-vertex induced path with 96 minority and 97 majority vertices has its two endpoints in the majority class. Assigning \(x\) to its selected vertices and \(e\) to its two endpoints satisfies every degree and endpoint constraint. The overlap equation retains exactly 94 vertices of the saved 96-set. Since the total minority count is 96, exactly two old vertices are omitted and exactly two new minority vertices are inserted. No extra ordering, crossing, connectivity, endpoint location, or symmetry condition is imposed.

Conversely, in any feasible selected graph every vertex has degree one or two, with exactly two degree-one vertices. Each connected component of a finite simple graph of maximum degree two is a path or cycle. The absence of degree-zero vertices and the total of two degree-one vertices force exactly one path component containing both endpoints; every other component is a cycle. These are induced components because degree is computed from all selected cube neighbours. Cube bipartiteness makes every cycle even. The 193 selected vertices do not by themselves force the path component to contain all 193 vertices.

## Added cycle cuts and witness handling

For an observed cycle vertex set \(C\), the inequality
\[
\sum_{v\in C}x_v\leq |C|-1
\]
is necessary for any induced path: selecting all vertices of that cycle would retain its cycle edges in the selected induced graph. The producer extracts actual selected connected components and checks degree two before adding such cuts. It does not discard a valid connected path when these cuts are used.

A feasible response is decomposed into connected components. Only a response without cycle components is decoded as a witness. The decoder then checks all 193 vertices, both endpoints, distinctness, and every pairwise cube adjacency. A disconnected feasible selection remains a relaxation solution and is used only to obtain further valid cuts. `UNKNOWN` or exhausted time remains unresolved.

## Prepared exact audit

`scripts/audit_degree.py --execute --tags degree,degree-rest --require-all-145` is prepared for execution after the worker terminates. It refuses to start while the worker lock exists and requires accepted terminal execution receipts. It reconstructs cube neighbours directly by Hamming distance, then checks every Boolean variable, linear coefficient, interval bound, and enforcement literal. Before added cuts, each model must have exactly 768 Boolean variables and 772 constraints: four cardinality equations, 256 endpoint-selection inequalities, and 512 positively guarded degree equations.

For each feasible iteration, the auditor independently reconstructs the selected graph, its endpoint degrees, components, and every added cycle cut. Each later exported model must contain exactly the earlier verified cuts. It also checks model/result/source/log pins, iteration ordering, native stdout correspondence, terminal statuses, any full witness, and the requested-base union. It writes `data/degree-audit.json` only after the complete audit passes and preserves any existing receipt.

## Source pins and limits

- `scripts/degree_search.py`: `ea4685761c79ae140d07023477c0bd9cbc67ac5301a6c4176079a5f923e59e60`
- `scripts/run_degree.py`: `01334f18dfc66804fb7fa2135c1d57b749d9ae9b3ac0f9b3f9edc8437a291a37`
- `scripts/audit_degree.py`: `55e746b2b52c468347d6b680ba7414c8eaea382a0fbc9673b93d194ea26ac8c2`

The audit checks the exact necessary models and saved native outcomes. It does not rerun a solver or replay a native contradiction proof, and it does not establish an end-to-end Lean connection to all concrete models. Any completed exclusion concerns exactly two minority replacements of the saved classes. A global upper bound does not follow.

## Executed saved-model audit

Status `PASS_DEGREE_MODEL_AUDIT`. Covered 145 saved bases and checked 145 exported models. Native statuses: `{'INFEASIBLE': 145}`. Verified added cycle cuts: 0.

All 145 saved exact-two-exchange families have native exclusions: `True`. Unqueried bases: `[]`. This records native evidence and exact model inspection, without independent native contradiction replay.

Auditor SHA-256: `55e746b2b52c468347d6b680ba7414c8eaea382a0fbc9673b93d194ea26ac8c2`. Receipt SHA-256: `134f56c89d649c5047b254fd32c0d2d0eda2eaab9400ef959b564ed7e4a6f9e6`. Complete evidence pins are in `data/degree-audit.json`.
