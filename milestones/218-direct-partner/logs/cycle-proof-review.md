# Checked cycle-cut preservation

`Cycle218.lean` passed Lean4.19.0 with two dependency reports. The accepted results derive a cycle-occupancy inequality from an actual induced path and distinct cyclically ordered vertices. They do not assume cycle impossibility as a premise.

## Statements and argument

`Cycle218.cycle_not_contained` takes:

- An actual `LayerJoining.InducedPath V R m`.
- A list indexed by `Fin (n+3)` of distinct ambient vertices.
- Symmetry of the ambient adjacency relation.
- Adjacency between every consecutive cycle pair and between its last and first vertices.

It proves that these cycle vertices cannot all occur in the path. Cycle length is at least three. Extra ambient edges between cycle vertices are permitted; an induced-cycle premise is unnecessary.

The proof constructs each cycle vertex's predecessor and successor and derives that they are distinct neighbours. It reuses the accepted `CycleCut196.noContainedDegreeTwo`: among the alleged path positions of the cycle vertices, choose a maximum. Both neighbours must precede it; inducedness forces each to be the immediately preceding position, contradicting their distinctness. This uses the actual path adjacency condition and finite cycle geometry.

`Cycle218.cycle_cut` additionally takes a Boolean selection and requires that every selected cycle vertex occurs in that same path. It proves

\[
\bigl|\{i:\text{cycle vertex }i\text{ is selected}\}\bigr|\le n+2,
\]

where the cycle has \(n+3\) vertices. In the Lean statement, the left side is the number of `true` entries in the finite selected-value list. Noncontainment gives an unselected cycle vertex, and elementary list counting gives the strict cardinality decrease. Distinctness makes this indexed count equal the number of selected cycle vertices.

Consequently, excluding a completely selected cycle preserves every fitting induced path. Applying this to a numerical cycle still requires identifying its distinct vertices and checking all consecutive and closing adjacency facts. The theorem does not check a solver's component extraction, serialized constraints, cycle discovery, exhaustion, or any particular native outcome. It gives no numerical snake bound. Parity facts were not added because they are unnecessary for this cycle inequality.

## Accepted evidence

- Source: `lean/Cycle218.lean`, SHA-256 `013c4a3afcf4d965d17e274a264775ceb197327c4d05ee70f77a67aa3de000d6`.
- Object: `build/Cycle218.olean`, SHA-256 `f29cf9400b91481d9668edad1462ee2b4ce515fe53b34f8d9bb4e99a55fae3e9`.
- Receipt: `data/Cycle218-audit.json`, SHA-256 `d90cc4c8d8a9efbbceaa8ca37de70059d6a3bbbfbe2029ae3d436db704ccb996`.
- Log: `logs/Cycle218-1794681204789359000/compiler.log`, SHA-256 `d6004c5537b4906b1f082ef81fb476590aa96f828be4c58d3e3fb2866c177024`.

Both exported results depend only on `propext`, `Classical.choice` and `Quot.sound`. The accepted receipt pins the imported sources, objects, logs, checker and dependencies. There are no admitted statements, new axioms or native decision calls.

The accepted run took2.140seconds with one compiler, `-j1 -s8192`, a60-second limit,256MiB private-memory ceiling,768MiB free-memory reserve and1GiB startup gate. Startup free memory was2,390,736,896bytes; the lowest sampled free memory was2,115,981,312bytes; maximum sampled compiler private memory was121,606,144bytes. No resource stop occurred. Sampling does not assert an unsampled exact memory maximum.

Two failed elaboration attempts are preserved at `logs/Cycle218-1794681146524597600` and `logs/Cycle218-1794681176573653500`, including their source snapshots and compiler logs. They concerned predecessor/successor arithmetic, a dependent rewrite and an unavailable tactic. The final source repairs these issues without changing theorem hypotheses. Failed dependency reports are not accepted proof evidence. The parent was notified immediately after the final compiler became terminal; no further compiler was launched.
