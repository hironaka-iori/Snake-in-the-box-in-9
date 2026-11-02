# Actual defined-graph walks with complete keys

Completion update: the module passed the parent compiler check. The source
hashes below record the initial design; successful compiler receipts preserve
the final checked bytes and any small proof repairs.

Status: source written and awaiting the parent's sequential Lean check. This subtask has not launched a compiler.

`lean/ActualGraphKeys98.lean` imports `CombinedEnvironment98` and uses the existing graph and state definitions. It introduces no new graph, row enumeration, state numbering, or endpoint function.

## Preserved information

The existing `DefinedGraph92.defined_actual_walk` and its closed-family specialization retain source and target identities. For a weight depending on the full row, the selected index must also carry its direction, history and count code.

The new interface retains all three facts at one common index:

```lean
(rows g).toList[edge.val]? =
  some (directionId p r, actualHistory p r, sixCode p r)
(sources g).toList[edge.val]? = some (actualState p r)
(targets g).toList[edge.val]? = some (actualState p (r+1))
```

The row order is exactly `(direction, history, six-count code)`. The index has type `Fin (rows g).size`. Consequently, a later row-weight argument can use the complete actual key at the same edge whose endpoints form the actual walk. No uniqueness of edges from their endpoint pair is assumed.

## Theorem interfaces

All names are in `Snake9.ActualGraphKeys98`:

1. `defined_actual_edge_key` takes an arbitrary existing diagram `g`, its `ClassMembershipFamily g` premise, `assignmentCheck = true`, the two reference-catalogue premises, a snake `p`, and $r+9\le m$. It returns one bounded edge index with the row-key equality and both endpoint equalities.
2. `defined_actual_key_walk` chooses those witnesses for every $i\in\operatorname{Fin}(m-8)$. The row and both endpoints use the same function `edge i`. The statement includes the empty step range for $m\le8$.
3. `retained_actual_key_walk` specializes the preceding theorem to the existing `retainedDiagram`, using `retained_class_family` and `assignment_checked`. Its only catalogue assumptions are `AllRefuted6K235` and `AllRefuted236`.

The proof of the first theorem reuses `Assembly87.actual_saved_edge` with `defined_graph_covers` and `defined_endpoint_columns`. The successful row lookup supplies the index bound. The walk theorem applies ordinary choice to these complete single-step witnesses. The specialization supplies the already checked family and assignment certificates.

The module requests three axiom reports, one for each exported theorem. No finite graph enumeration is evaluated by these proofs.

## Remaining scope

The new interface concerns the defined graph `rows retainedDiagram`. It makes no equality claim about an external NPZ row file. It preserves raw state values and all components needed for key-dependent weights.

The two reference catalogues remain explicit premises. A row-weight formula, equality of numerical weights to that formula, a finite potential certificate, potential-range accounting and the final numerical bound are separate obligations. In particular, the new walk theorem does not discharge either reference catalogue.

## Source pins

| Source | SHA-256 |
|---|---|
|98 `lean/ActualGraphKeys98.lean`|`14b8bd7086693be64c028a1d05989855c1d9f77c71b8b2ebbef8f819aea55766`|
|92 `lean/DefinedProofGraph.lean`|`68f9edf0ac8b3ff140b7fba30b6c311553db3da31c7e4c3bf53c45b1f1e3de7e`|
|87 `lean/ArrayAssembly.lean`|`4ec3ab0d6a0950d77b391acdfb790a8f31b485e4eed8a4bb0aa4e44bfb6fd066`|
|92 `lean/CloseBatch.lean`|`5a9034c0b38906ec03747071c2840b6e12fb3307b4fd2a5788faaa35de164e3a`|
|98 `lean/CombinedEnvironment98.lean`|`3f728c64648bef2c4a4a88859601c8f501281e5ad4ffb9d77689fc1fb2663c01`|

These pins record the inspected bytes. The parent owns compilation receipts and combined-environment validation.
