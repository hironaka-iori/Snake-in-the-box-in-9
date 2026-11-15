# Residual-component pruning: source preparation

Status: source only. No compiler, native worker, solver or software tests were run. This is a necessary condition for constructing the second replacement, with no new numerical exclusion or global bound claimed.

## Reuse and statements

A targeted review of the accepted joining and replacement sources in rounds 188, 193, 224 and 225 found no component-containment theorem to reuse. `Residual226.lean` therefore uses the existing actual indexed path structure from `LayerJoining` and a closed-set characterization of the component, without introducing a reachability definition. `ResidualCapacity226.lean` reuses `Capacity209.distinct_length_le` for finite capacity.

The first module contains four statements:

1. For an actual induced path, if (i\le b), (c\le j) and (b+2\le c), the vertices at (i,j) differ and have no edge from the first to the second. This derives full cross-separation from actual path geometry when there is at least one retained index between the closed replacement intervals.
2. A set containing the initial path vertex and closed under steps to allowed vertices contains the entire actual path. The proof is induction on its index, using the path's induced-adjacency theorem to obtain each consecutive edge.
3. If every second-path vertex is allowed and is unequal and nonadjacent to every first-prefix vertex, its whole path lies in any set containing its initial anchor and closed under residual edges. Taking that set to be the residual connected component gives the desired necessary condition, including membership of the final anchor.
4. If the first prefix is extended, the residual allowed set shrinks. Each vertex avoiding the larger prefix also avoids the smaller one.

The capacity module derives injectivity of any duplicate-free list of selected path positions from the actual path's injectivity, then applies finite-list capacity. It gives the total bound (n+1\le |C|) when the supplied index list has length (n+1), and the corresponding bound for each selected colour class inside the component. A duplicate-free component enumeration is needed to interpret list length as exact component cardinality; duplicated pool entries would merely weaken the necessary bound.

## Scope of component and colour interpretation

The component premise is explicit closure under every residual adjacency step, together with membership of the initial anchor. It does not assume containment of the whole path. The proof works for any such closed set, so minimality of a connected component is unnecessary. A concrete BFS enumeration must still be connected to that closure premise and to the actual residual adjacency relation.

For a bipartite cube path of (n) edges, consecutive vertices alternate colour. Thus the initial colour occurs (lfloor(n+2)/2\rfloor) times and the other colour (lfloor(n+1)/2\rfloor) times. The native formula in the inspected worker agrees with this count. The new Lean source proves the capacity statement for a selected colour class; it leaves the concrete alternating-index enumeration and these closed count formulas as explicit remaining assembly work. It does not claim that those numerical arrays have been checked by Lean.

For fixed anchors and target length, extending the first prefix cannot restore a deleted anchor, a connection, total capacity or colour capacity. Indeed, an actual second path surviving the extended prefix would also survive the old prefix and hence would lie in the old closed component with the same required counts. This conclusion uses residual inclusion and the preceding necessary conditions; it does not require reusing the same BFS queue or search order.

## Anchor boundary and current data

Deleting the closed neighbourhood of every vertex of the first prefix requires separation from the entire second path, including its anchors. The condition (b<c) alone is insufficient: if (c=b+1), the two retained anchors are consecutive and adjacent. Shared anchors also require an exception. The general derivation therefore requires (b+2\le c), or an independently supplied full cross-separation statement.

The frozen width-43 input has 294 contexts with minimum anchor-index gap 52; context 22 has gap 80. Consequently this boundary issue does not require a correction to those saved contexts. This was a bounded read of the saved interval metadata, not a search run or review of the changing DFS frontier.

## Dependencies and remaining assembly

- `LayerJoining.lean`: source SHA256 `30687e190d96818b64569e90faaff50eba28acf7698e4ffa8c6d89d8fe640a74`.
- `Capacity209.lean`: source SHA256 `70f9b06815716432b38c89b7bd2955f6551b593d869bb61116ed0fbf4329c2ac`.
- Inspected `regions43.json`: SHA256 `b1cf54d596bcd8e04162fef9741dca90eed03ab03e78089318614215d1b9b3da`.
- Inspected `connected_pruned.py`: SHA256 `609726b4d5679e0f1fbb287af7f025b3c5d1508aa5f195be3510964e3f58db80`. Only the mathematical pruning conditions were inspected; this is not a complete worker audit.

Prepare/check `Residual226` first, then `ResidualCapacity226`, after importing the existing accepted dependency receipts and objects. Four and three axiom reports are requested respectively. The concrete bridges still needed are the two interval embeddings in an actual simultaneous candidate, residual-domain equality, complete BFS closure, duplicate-free component/position enumeration and the alternating-colour count assembly. No accepted source or native script was changed.

## Zero-crossing face capacity

The additional `ZeroFace226.lean` uses the existing Boolean `changes` function from accepted `CutParity221`. A list induction proves that zero true changes force every coordinate value to equal its initial value. The coordinate version applies to any finite vertex walk. Composing this with the actual-path colour-capacity theorem gives the necessary bound (n+1\le |D\cap F|) for a path with zero changes of that coordinate, where (F) is its initial face.

The actual-path statement uses `List.ofFn p.vertex`, with its first coordinate supplied again as the starting value. The initial duplicate contributes no change; the remaining comparisons are the actual consecutive coordinate values. The generic source requires an explicit zero count of this Boolean change list. Relating that count to the native coordinate-8 XOR counter and certifying each frozen face enumeration are separate concrete obligations.

Therefore an independently verified face size below 44 excludes a 43-edge zero-crossing replacement in that face. Combining this with endpoint crossing parity and a total budget of two can restrict the allocation to first zero, second two when both second anchors are in that face. This note does not certify the parent's numerical count over all 24 contexts or any native exclusion.

Check `ZeroFace226` after the two residual modules and after importing accepted `CutParity221` (source hash `24f789fd4c9f293925c190debe679ba4e535948c01bb664e061ac2a3cde37912`). It requests three reports. Current prepared source hashes:

- `Residual226.lean`: `2e3378ae7c7c57d4214fdeff618208fca93a1c455bfde848310edde500263e45`.
- `ResidualCapacity226.lean`: `65e765c5aa4860e8b9cb44d72864af02c28df600d548c41cd4b7b473c977dc60`.
- `ZeroFace226.lean`: `48af868ca4539ef982c9f6e19761eb212db66c6f916739373a695aa8471f162b`.
