# Joint two-exchange model review

## Source conclusion

No blocking defect was found in the inspected model. It represents exactly the induced 193-vertex paths in the actual nine-dimensional cube whose 96-vertex minority class retains 94 vertices of the chosen saved 96-set. Both omitted vertices, both inserted vertices, the entire majority class, path order, and endpoints are free. The four selected base classes are a heuristic sample, not a complete cover of the 145 saved classes.

This is a source review. The independent saved-model auditor is prepared but has not been executed by this reviewer. No solver, compiler, software test, or native-worker operation was performed.

## Soundness

For a cube edge with endpoint-selection variables \(x_v,x_w\) and directed arc variables \(f,b\), the three inequalities give
\[
f+b=x_vx_w.
\]
This follows directly from the four Boolean endpoint cases. In particular, an arc cannot touch an unselected vertex, both orientations cannot be selected together, and every adjacency between selected vertices must appear once in the directed circuit.

Each cube vertex has the self-loop literal \(\neg x_v\). Thus unselected vertices take their loops, while all selected vertices belong to the unique nontrivial circuit. The dummy vertex has no self-loop, so it belongs to that circuit. Its arcs are incident only with selected majority vertices. The local `cp_model.py` documentation at lines 578–586 states the single-circuit and excluded-node self-loop semantics used here.

There are exactly 193 selected vertices. A two-cycle consisting of the dummy and one cube vertex would leave the other selected vertices without the required single circuit, so it cannot satisfy the model. A directed two-cycle on a cube edge is separately excluded by \(f+b\leq1\). Removing the dummy therefore leaves one path through all selected vertices, with distinct majority endpoints. Every selected cube adjacency is used by this path; consequently it has no chord. The fixed counts give 192 edges and two minority replacements.

## Completeness

Take any induced 193-vertex cube path with the prescribed minority overlap. Its endpoints have the majority parity because the two colour classes have sizes 97 and 96. Orient the path in either direction, select its vertices and directed edges, join the dummy to the first vertex and the last vertex to the dummy, and choose the self-loops at all unselected vertices. An induced path has precisely its consecutive pairs as selected cube adjacencies, so all three edge inequalities hold. The dummy circuit and all three cardinality equations then hold. Hence the model omits no path in the stated family.

The reused round-199 source employed the same optional-vertex circuit mechanism. Its quotient graph, endpoint-order restriction, seed-retention inequality, branch cases, clique cuts, square cuts, and solution hints are absent from the round-235 model. No quotient interpretation or symmetry assumption is required here.

## Decoding and statuses

For a feasible response, the decoder requires exactly one selected start and end, follows the selected cube arcs, and checks the complete 193-vertex path for distinctness and every pairwise adjacency. It independently checks both removed and inserted minority vertices. The same-endpoint degenerate case would fail the length check even before the pairwise verification.

`COMPLETE_QUERY_BATCH` means every requested base was queried; it does not mean the queries were resolved. `UNKNOWN` remains unresolved. `INFEASIBLE` would exclude only its particular exact-exchange family and remains native solver evidence. A wrapper interruption would prevent this auditor's accepted-execution gate. No global bound or complete two-exchange census follows from these four queries.

## Prepared independent audit

`scripts/audit_joint.py --execute --tag joint` is ready for use after the native worker terminates. It refuses to start while the worker lock exists and requires an accepted, terminal execution receipt. It verifies source/input/result/log pins and reconstructs all expected constraints from direct Hamming adjacency on the 512 vertices. Each complete model must contain exactly 5,632 Boolean variables, 7,427 linear constraints, and one circuit with 5,632 arcs. Every field of the exported text is consumed; extra objectives, constraints, hints, or restrictions are rejected.

The audit compares normalized linear constraints as multisets and reconstructs the full circuit including negative self-loop literals, both orientations of every cube edge, and all majority-to-dummy arcs. It checks model counts and hashes, native statuses, stdout correspondence, any decoded witness by all 18,528 vertex pairs, and the exact queried prefix. It uses only the Python standard library, prints a JSON receipt, and appends its successful execution outcome below. Execution is pending.

## Inspected source pins

- `scripts/joint_search.py`: `a393ec026d4fff96fe8609595da8cb69b51c85d5470a01efbdc374f82ab42802`
- `scripts/run_joint.py`: `b4cb37bda5471cf884fe413b742ddeefd074a52c41b28a70bb5a6a226983a3d6`
- `data/bases.json`: `ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b`
- `../199-parent-diversity/scripts/circuit_search.py`: `94eac82db3680313a17b1a16f72c0b2656f77c65814ac1043429685096a20997`

The execution receipt will pin the auditor and the locally inspected circuit API source. End-to-end Lean verification of the complete model and independent native contradiction replay are outside this review.

## Saved-model audit execution

Status: `PASS_SAVED_JOINT_MODEL_AUDIT`. Inspected 4 complete exported models, each with 5,632 Boolean variables, 7,427 exact linear constraints and one circuit constraint. Native statuses: `{'UNKNOWN': 4}`. Batch status remains `COMPLETE_QUERY_BATCH`.

Verified witness: `None`. Unqueried requested bases: `[]`. Unknown results remain unresolved. No native contradiction was independently replayed.

Auditor SHA-256: `e9a511b6e5e6af92d2125e4a01ddf6914c2f8dad63a309efad392b7cd5b9d30c`. Full source/model/log pins are in the JSON stdout receipt.

## Saved-model audit execution

Status: `PASS_SAVED_JOINT_MODEL_AUDIT`. Inspected 4 complete exported models, each with 5,632 Boolean variables, 7,427 exact linear constraints and one circuit constraint. Native statuses: `{'UNKNOWN': 4}`. Batch status remains `COMPLETE_QUERY_BATCH`.

Verified witness: `None`. Unqueried requested bases: `[]`. Unknown results remain unresolved. No native contradiction was independently replayed.

Auditor SHA-256: `e9a511b6e5e6af92d2125e4a01ddf6914c2f8dad63a309efad392b7cd5b9d30c`. Full source/model/log pins are in the JSON stdout receipt.
