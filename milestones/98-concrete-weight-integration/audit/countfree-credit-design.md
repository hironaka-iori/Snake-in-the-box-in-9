# Count-free credit lookups

Completion update: the module passed the parent compiler check. The source
hashes below record the initial design; successful compiler receipts preserve
the final checked bytes and any small proof repairs.

Status: source written; the parent controls the combined import environment and sequential Lean check. This subtask has not launched a compiler. The source imports the parent's `Port98CombinedCatalogue`, together with `GraphShareLookup` and `ActualDirectionIds`.

The module is `lean/CountFreeCredits98.lean`, namespace `Snake9.CountFree98`. It defines four executable functions:

- `completedFloor cs`: the five completed representative-word floors.
- `conditionalFloor cs`: the completed floors plus five explicitly conditional improvements.
- `completedCredit di`: `completedFloor (graphShape ((extensions.getD di []).drop 3))`.
- `conditionalCredit di`: the same exact graph lookup with `conditionalFloor`.

The lookups depend only on the direction component of the full graph key. They neither discard nor infer the history and count components used by other credit families. Their contribution can later be combined with those families by taking the maximum.

| Six-direction representative | Completed floor | Conditional floor |
|---|---:|---:|
|012031|16|16|
|012032|0|16|
|012034|0|18|
|012301|0|16|
|012304|16|16|
|012310|12|12|
|012314|16|16|
|012340|0|16|
|012345|12|16|

Both tables return zero outside these representatives. All values are integer shares at scale 12.

## Local evidence and explicit premises

The completed cases012031,012304,012310,012314 use the existing `Snake9.CatalogueIntegration73.canonical7300`, `canonical7304`, `canonical7305`, and `canonical7306` theorems. The completed012345 floor12 is obtained from `Snake9.LocalWindow.ShareWindow12.refuted`, whose cap is11 and whose five bounds are all $(0,21)$. The generic adapter `share_bound_of_either_canonical_match` supplies either canonical orientation.

The conditional theorems retain these five parameters exactly:

```lean
(h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
(h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
(h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
(h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
(h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
```

Here `broadBounds` is five copies of $(0,21)$. Case7302 uses cap17, giving floor18. The old `partial_catalogue_share` and `graph_catalogue_share_bound` use cap19 for this case; the new module therefore constructs the weaker conditional table directly from the five stated premises.

These are count-free statements. Neither lookup reads a truncated count symbol, so no saturated symbol is converted into an exact count.

## Actual-window transport

For a snake $p$ with $m$ edges, an edge position $r$ satisfying $r+9\le m$ has six-transition share window starting at $t=r+3$. Its five charged centres are

$$
t+1,\ldots,t+5=r+4,\ldots,r+8.
$$

`direction_decode` identifies the stored nine-direction word at `directionId p r` with `canon (dsOf p r 9)`. The already checked `actual_suffix_lookup` then identifies the graph's lexicographic canonical suffix representative with `selectedShape (dsOf p (r+3) 6)`. The new local selected-shape bounds use `selectedShape_mem_and_match`, retaining the correct forward or reversed canonical match.

The exported actual-key theorems are:

```lean
actual_completed_credit {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    completedCredit (directionId p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum
```

`actual_conditional_credit` has the same conclusion with `conditionalCredit` and the five refutation parameters above. The module requests printed axiom reports for these two theorems and for `canonical_distinct_completed`, `completed_selected_bound`, and `conditional_selected_bound`.

The scope is a pointwise credit bound on an actual graph key. This source does not establish the five pending refutations, a complete graph weight equation, a potential inequality, endpoint accounting, or a new numerical snake bound. A standard-axiom report for a theorem with parameters does not discharge its explicit refutation premises.

## Inspected source and receipt pins

| Input | SHA-256 |
|---|---|
|73 `lean/CombinedCatalogue.lean`|`19eda80b918cf9af64183980229e21811c5a90f316e501f0e0757c9ebc8aaa2d`|
|73 `data/integration-audit.json`|`d90a4c77464c10db1d62a8b70cb7f14bb15fac5162ca01255128fd727d5d1d01`|
|75 `lookup/lean/GraphShareLookup.lean`|`1298f44918498396943aa8e1b1e7ef46ea173f62fd4859dec74afa13c0431e40`|
|75 `lookup/data/proof-audit.json`|`08d40929a73eacb66551e311eb271ef6fc524a5f882faef6c0c209b9f68689ad`|
|73 `adapter/lean/ConditionalCatalogueDispatch.lean`|`fd4b3833567fb42c7fb31e6987d51324cda6492193b9fbf702d2efa4666839ff`|
|72 share12 `lean/LocalWindowCnf/ShareWindow12.lean`|`16f6e3cc5917d156e12cc0cfdc9c3dc86bc5eb69ec359ed9a29c74a408f79b0c`|
|72 share12 `lean/Share12/Refuted.lean`|`decbe2456e49f3feadc0e859f5448f00f3dbd3eb5ca00510c6021bf6e47330c4`|
|77 `lean/ActualDirectionIds.lean`|`f0da81617ccbcce214f0a9aa59e57234dc2379eb3671300cfedf9fa6daceacf9`|

The historical73 receipt reports `PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET`; the75 lookup receipt reports `PASS_EXACT_GRAPH_SHARE_LOOKUP`. Their reuse in milestone98 is subject to the parent's new combined check.
