# Defining the proof graph from diagram acceptance

Bounded mathematical/source audit, 2026-11-02. No compiler, generator, solver, potential replay, or graph reconstruction was run. Only this report was written.

## Viability verdict

Yes. Defining the Lean proof graph directly from the 791 block bindings and the accepted count codes is a sound reduction. Its endpoint columns can be defined by mapping the existing `rowSource` and `rowTarget` functions over those rows. Coverage and endpoint identities can then be proved from the numeric-diagram theorem and those definitions, without identifying a separately imported NPZ row or endpoint array.

This removes an unnecessary artifact-equality obligation **provided that the complete weight/credit interpretation, edge-potential inequalities, potential range and final budget are proved for this defined graph**. An existing certificate checked only on the NPZ graph cannot be transferred merely because the new graph is intended to represent the same data. Its numerical potential values can be reused as candidate data and checked anew on the defined graph.

No circular assumption is required. The graph is fixed finite data; the retention theorem proves actual candidates enter it; the potential certificate constrains all its edges independently. The graph may contain additional unrealizable edges. Extra edges can weaken or invalidate a proposed potential certificate, but do not invalidate an upper-bound argument once that certificate passes. Neither exact equality to `numericKeep` nor realization of every graph edge by a snake is needed.

## Minimal next definition and theorem

The following is a proposed construction, not checked source:

```lean
def proofRows : List Row :=
  savedBlockClasses.flatMap fun bc =>
    ((List.range 46656).filter fun c =>
      diagramEval retainedDiagram (savedRoots.getD bc.2 0) (digits c)).map
      (fun c => (bc.1 / 75, bc.1 % 75, c))

def proofU : List Nat := proofRows.map rowSource
def proofV : List Nat := proofRows.map rowTarget

theorem defined_graph_covers
    (hdiagram : ∀ di q c, di < 505 → numericKeep q di c = true →
      Assigned di q ∧
      diagramEval retainedDiagram
        (recordedClassRoot (chosenClass di q)) (digits c) = true) :
    RetentionCover retainedKeep proofRows
```

The proof uses `Assigned` to obtain the saved block/class binding and saved root equation. Unfolding `savedBlockClass`/`savedRootForBlock` gives a matching entry of `savedBlockClasses` and the root lookup needed by the filter. `c < 46656` gives range membership. The bound `q < 75` identifies `(75*di+q)/75 = di` and `(75*di+q)%75 = q`. `List.mem_filter`, `List.mem_map` and `List.mem_flatMap` then produce the full key. The pending completed numeric-diagram theorem supplies `hdiagram`; the existing generic class-family interface can be retained as a premise until that assembly succeeds.

Set `rows := proofRows.toArray`, `U := proofU.toArray` and `V := proofV.toArray`. The endpoint-map premises of `87/lean/ArrayAssembly.lean` follow by the standard list/array conversion identities. `actual_saved_edge` and `actual_saved_walk` can be instantiated with these objects; their names do not require that the arrays came from NPZ. A direct membership lemma can precede the `RetentionCover` theorem if it simplifies the implementation.

A depth-recursive accepted-code enumerator may replace the filter for efficiency after proving its equivalence to `diagramEval`. Terminal 1 must enumerate every remaining suffix; child symbols are 1 through 6 and row position zero is depth metadata. This is an implementation choice within the same reduction. No 127-class equality to independently exported NPZ code lists is needed when the proof graph itself is defined this way.

## Vertex encoding and compression

The actual-state encoding already uses the builder's original numeric namespace. `75/numeric/lean/CountStateCode.lean` defines

\[
\operatorname{stateCode}(s,q,c)=
\begin{cases}
7776s+c,&q=0,\\
1026432+7776(q-1)+c,&q>0.
\end{cases}
\]

For valid inputs it is below 1,601,856. Nonzero histories store their compatible shape implicitly. This merging of redundant shape information is built into the checked actual-state and endpoint formulas, so it does not require an injective encoding of every unrestricted `(shape,history,counts)` triple.

`78/lean/StateWalk.lean` defines

\[
\begin{aligned}
\operatorname{edgeSource}(q,d,c)&=
 \operatorname{stateCode}(\operatorname{sourceId}(d),q,\lfloor c/6\rfloor),\\
\operatorname{edgeTarget}(q,d,c)&=
 \operatorname{stateCode}(\operatorname{targetId}(d),\operatorname{builderNext}(q,d),c\bmod7776).
\end{aligned}
\]

`actual_source_state` and `actual_target_state` identify these with consecutive values of `actualState`; `actualState_lt` and `encoded_actual_step` include the required window bounds. The NPZ builder in milestone 70 uses exactly these original state formulas. `np.savez_compressed` is storage compression and does not renumber vertices.

There is a different, temporary renumbering in `73/scripts/evaluate_checked.py`: cyclic vertices are collected into `active`, then mapped through `index` for Howard's minimum-cycle-mean search. The returned cycle indices are mapped back to original edge indices. Crucially, the exported potential is subsequently built as `pi = zeros(N)`, relaxed on the full original `U,V` arrays, and checked on every edge. The current saved model records `N = 1601856`. Thus its potential is indexed by the original raw state IDs, not by the temporary cyclic IDs.

Reuse those full-state potential values as a proposed total function on original state IDs, followed by a new check against `proofRows`. If instead a cyclic-only or otherwise compressed potential is reused, it needs a checked map and an extension covering every state used by actual finite walks, including transient vertices. A cycle-only check is insufficient for the finite-path bound.

## Obligations that remain

1. **Actual retention.** Complete the class-family/numeric-diagram assembly and prove the generic construction theorem above. `actual_numeric_keep` and the existing actual-walk assembly retain `AllRefuted6K235` and `AllRefuted236`. Defining a graph does not discharge those reference-catalogue premises.
2. **Weights and local credit.** Define a total weight `W : Row → Nat` from explicit checked rules, then prove its value on each actual full key is at most the admissible local charge. Where alternative lower share estimates concern the same contribution, take their maximum, not their sum. Full-key lookup is essential: different `(direction,history,count_code)` rows can share endpoints and have different weights. Reusing NPZ weight positions would reintroduce an ordering/equality dependency unless those positions are independently justified.
3. **All-edge potential certificate.** For a proposed numerator `P`, denominator `D > 0` and potential `pi`, check on every row of the newly defined graph that

   \[
   P+\pi(\operatorname{rowTarget}(k))
   \le D\,W(k)+\pi(\operatorname{rowSource}(k)).
   \]

   The generic `61/lean/FinitePotential.lean` already provides `edge_of_check` and `path_bound`. The final checker may use the full row list or a proved equivalent decomposition by block and accepted suffix; it must include every accepted edge. Candidate values and recorded means are not this certificate.
4. **Potential endpoints and budget.** Prove the potential range on every relevant actual state, including the first and final state. Total default-zero lookups are acceptable only when their exact semantics and range are included in the theorem/check. Combine the finite-path inequality with the actual local-credit summation and empty-square budget. Existing small-length and boundary hypotheses remain. A tight cycle is unnecessary for an upper-bound certificate, though it can prove that a particular graph's minimum mean is attained.

This remains within the empty-square route. The existing model's mean 483 and range 551 are candidate numerical data for replay; this audit establishes neither their certificate on the newly defined graph nor a new upper bound.

## Source pins and review boundary

Paths below are relative to `E:/Snake-in-a-box/milestones/`. These hashes were recomputed during this bounded review.

| Source | SHA-256 |
|---|---|
| `75-exact-history-bridge/numeric/lean/CountStateCode.lean` | `76511c647e280e8da66998622e1ac9d673c10ae8ca0dcd1396fd2724bfb7a1bc` |
| `78-numeric-history-transition/lean/StateWalk.lean` | `f9c477e3271a37ba5735550a87da677205517e5883362403a6fd6bf46e954e56` |
| `87-retained-array-membership/lean/ArrayAssembly.lean` | `4ec3ab0d6a0950d77b391acdfb790a8f31b485e4eed8a4bb0aa4e44bfb6fd066` |
| `92-full-witness-batch/lean/ContextAssignment.lean` | `059e6cf2bc2167920ec59157c2d7fb261fb30a5134cfae224f9e4993c05ca157` |
| `70-proof-supported-share-model/scripts/build.py` | `bffe9f3d541a807841d564a85bc3f5d2523ae73ee7b8218b79facdac9a4987db` |
| `73-countfree-share-catalogue/scripts/evaluate_checked.py` | `be1a41ac42427c02f61007b1b7e62983bc248880827505e0481e25473ddbd29d` |
| `61-critical-family-share/lean/FinitePotential.lean` | `7dfbe61e69208dce373f4a18faeedadeb904c85a39027c9df8ae7a0a86fd716a` |
| `73-countfree-share-catalogue/data/proved-model.json` | `785956145396df7cf6230c446a9e7469b7c4b1713c6cf70d21a9091f1c8f7907` |

The potential hash recorded by that model is `90ee55c9e675275f506b947223e36cfeddafc3fcb0a56d61122a5d3ab81e35a0`; the compressed potential was not decoded or replayed in this audit. The proposed reduction is mathematically sound under the explicitly listed obligations. Its construction theorem and complete certificate have not been implemented or checked by this review.
