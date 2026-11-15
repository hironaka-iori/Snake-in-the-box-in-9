# Actual-path subset-forest proof

`Forest220.lean` passed Lean on its first compiler attempt after the parent released the native slot. The guarded run took 3.181 seconds. No solver or software tests were launched for this proof.

The accepted `Capacity209.distinct_length_le` supplies finite-list injection counting. `ExchangeAccounting190` was inspected, but its component deductions assume degree and edge accounting and do not supply the required actual-path subset bound. `RadiusThreeForest` checks a particular finite witness rather than a general subset theorem. The new argument therefore reuses the capacity lemma and `LayerJoining.InducedPath`, without introducing definitions or a graph framework.

## Checked actual-path argument

Take selected positions in an actual induced path, and a duplicate-free list of ambient edges between those positions. Each edge is represented once by its two increasing path indices. The actual adjacency fact and inducedness imply that these indices are consecutive; consecutiveness is derived rather than assumed.

If one selected position is marked, assign every counted edge the endpoint farther from that position along the path. An edge before the marked position is assigned its earlier endpoint; an edge at or after it is assigned its later endpoint. These assignments are injective because every counted edge joins consecutive indices. None is assigned the marked index. Appending that index to the assigned list and applying the accepted finite capacity lemma proves

\[
\text{number of counted edges}+1\le\text{number of selected positions}.
\]

The empty case gives the weaker inequality without the extra one. `subset_forest_bound` combines both cases using a Boolean marked-selection indicator, yielding

\[
Y+x_v\le X.
\]

The membership implication required for a true indicator is explicit. For a fixed ambient subset \(U\), take the selected list to be the duplicate-free path indices whose vertices belong to \(U\), and take the edge list to enumerate all ambient selected edges in \(U\), oriented by increasing path index. Path injectivity identifies these position counts with vertex and edge counts. For \(v\in U\), an indicator \(x_v=1\) gives a selected path index, discharging the membership implication. When \(x_v=0\), that implication is vacuous. The edge list need not be complete for the stated upper bound; completeness is needed when identifying its length with the native model's entire induced-edge count.

This supplies an actual induced-path bridge, not a premise asserting that the selected subgraph is already a forest. The numerical subset arrays, edge enumeration and correspondence to native variables remain separate application obligations. The selected list may contain duplicate indices in the generic inequality, which only weakens its right side; use its canonical duplicate-free enumeration to interpret it as set cardinality.

`degree_boundary_iff` additionally proves over signed integers that under

\[
2X-E=2Y+B,
\]

the inequality \(Y\le X-x_v\) is equivalent to \(B+E\ge2x_v\). This algebraic statement does not supply the degree-sum identity; that identity must follow from the actual model's degree equations and counting conventions. Endpoint count is \(E\), internal-edge count is \(Y\), and boundary-edge count is \(B\).

The four exported theorems are `selected_edges_add_one_le`, `selected_edges_le`, `subset_forest_bound`, and `degree_boundary_iff`. The first three dependency reports contain only `propext` and `Quot.sound`; the arithmetic equivalence also uses `Classical.choice`. No new axioms, omitted proofs or native decision procedure occur. No numerical bound, min-cut result or certified native enumeration is claimed by this module.

## Verification record

- Receipt: `data/Forest220-audit.json`, SHA256 `d3783042fef8077362851b4e362d3729fc45357cd6ba0eff212a52d06d968bc8`.
- Source SHA256: `8c2ddfeb5871c85f5c47348d19567f2a3b7075c08427b204602ebf30db1c6e9d`.
- Accepted object SHA256: `cb0fd0ac135163ead02ba8a583ece3cc82a35f1d9a346c37140d90972804861d`.
- Compiler log: `logs/Forest220-1794708567904739900/compiler.log`, SHA256 `319b44c491b7839a2f0ca81c53bc91bef260a8be221d081fbd46542dfdeef0ba`.
- The receipt pins the execution plan, checker, native resource helper, accepted `LayerJoining` and `Capacity209` imports, their source/object/log receipts, and their transitive dependencies.
- The run used one Lean process with `-j1 -s8192`, a 60-second limit, a 256 MiB private-memory limit, and a 768 MiB free-memory reserve. Startup free memory was 1,783,934,976 bytes; the smallest recorded free-memory sample was 1,522,962,432 bytes, and the largest recorded compiler private-memory sample was 61,251,584 bytes. All sampled resource checks passed. These are sampled values, not continuous peak measurements.
- There were no failed compiler attempts. The compiler is terminal and the native slot has been returned to the parent.
