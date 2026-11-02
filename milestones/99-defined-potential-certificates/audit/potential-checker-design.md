# Potential certificate checker

Status: source written in `lean/PotentialChecker99.lean`; no compiler or finite certificate evaluation has been run by this subtask. The parent owns compilation and concrete certificate generation.

The module imports `PotentialAssembly98` and `BalancedLookup`. Its namespace is `Snake9.PotentialChecker99`. It preserves the exact defined graph, raw state indices, full row key, and weight argument order.

## Executable tests

- `checkInterval test start count` checks the half-open interval $[\mathrm{start},\mathrm{start}+\mathrm{count})$ using `List.range` and `List.all`.
- `edgeCheck w P π di q code` returns true for a rejected diagram code. For an accepted code, it checks
  $P+\pi(\operatorname{edgeTarget}(q,di,code))\le w(q,di,code)+\pi(\operatorname{edgeSource}(q,di,code))$.
- `contextCheck w P π di q` checks all codes below46656 for that context.
- `graphCheck w P π` is the complete executable specification over directions below505 and histories below75.

The arbitrary function `w` has argument order `(history,direction,code)`, matching `Weights98.weight floor`. The test's context arguments use `(di,q)`. The condition is exactly `diagramKeep retainedDiagram di q code = true`; it does not substitute a different retention predicate.

The intended certificate method uses separate context and interval theorems. It should not reduce the entire `graphCheck` in one kernel computation.

## Chunk and context assembly

`checkInterval_iff` gives the exact bounded meaning of a successful interval check. `checkInterval_join` combines adjacent intervals. `checkInterval_of_chunks` combines separate equal-width chunk proofs by induction.

`contextCheck_of_chunks` requires

$$
\mathrm{chunks}\,\mathrm{width}=46656
$$

and a checked interval starting at $j\,\mathrm{width}$ for each $j<\mathrm{chunks}$. Thus216 chunks of216 codes form one possible complete partition. This is a proposed evaluation granularity, with no performance measurement claimed here. `checkInterval_join` also permits differently sized intervals.

`contextCheck_missing` handles a context with `savedBlockClass (75*di+q) = none` symbolically. Such a block rejects all codes and needs no46656-code computation.

`row_potential_of_context_checks` takes successful context checks for every bounded direction and history. For a member of `(rows retainedDiagram).toList`, it unfolds only the outer row definition and applies the existing `generated_row_iff` theorem. That theorem supplies the three key bounds and diagram acceptance. The checker then yields the row inequality. The proof never evaluates the large `generatedRows` expression.

`weight_potential_of_context_checks floor P π` specializes this result to the exact weight function. Its conclusion is precisely the `hpotential` premise of `PotentialAssembly98.actual_potential_bound`:

```lean
∀ row ∈ (rows retainedDiagram).toList,
  P+π (rowTarget row) ≤
    weight floor row.2.1 row.1 row.2.2+π (rowSource row)
```

`graphCheck_sound` provides the corresponding extraction from one complete Boolean certificate, when such a certificate is supplied.

## Fast lookup and potential range

The interval checker accepts any Boolean test. `checkInterval_transfer` transports a successful optimized check to the original test from pointwise equality on that interval. This allows the parent's fast diagram lookup to replace `diagramKeep` after proving the required equality. The same mechanism can cover optimized weight or potential lookup implementations. No equality outside the checked interval is required.

The existing balanced-table interface proves total lookup equality, including defaults, from its validity and flattening premises. This module creates no new lookup tree or potential definition. The parent's completed and conditional potential functions can be supplied directly.

`min_potential_range` proves

$$
\forall s<1601856,\quad \min(R,\mathrm{raw}(s))\le R
$$

for any natural-valued raw function. This discharges the range premise without enumerating state values. Clipping does not establish the edge inequalities: every accepted edge still needs its corresponding check.

## Remaining obligations and audit names

The twelve requested axiom reports are `checkInterval_iff`, `checkInterval_join`, `checkInterval_transfer`, `checkInterval_of_chunks`, `edgeCheck_sound`, `contextCheck_sound`, `contextCheck_of_chunks`, `contextCheck_missing`, `row_potential_of_context_checks`, `graphCheck_sound`, `weight_potential_of_context_checks`, and `min_potential_range`.

Compilation remains pending. Concrete accepted-edge checks, complete coverage of bounded contexts, and any fast-test equality proofs are not supplied here. No numerical snake bound is claimed. The two reference-catalogue premises and any conditional count-free premises remain in the downstream theorem from98; the finite potential checker neither adds nor discharges them.

## Source pins

| Source | SHA-256 |
|---|---|
|99 `lean/PotentialChecker99.lean`|`2973e8ab538350958d684734b9949faccbb7e61913d03838a01e6aa3b2d5d89e`|
|98 `lean/PotentialAssembly98.lean`|`bd5bceccfeda6c7b5d2a602dac0326508dfa63ceb2f1a58d69ff99778aa18eb4`|
|89 `lean/BalancedLookup.lean`|`b956f192953c15554de5c74dbcd946bcabda4c2d392f85b5b65d965f07fe5f2e`|
|92 `lean/DefinedProofGraph.lean`|`68f9edf0ac8b3ff140b7fba30b6c311553db3da31c7e4c3bf53c45b1f1e3de7e`|
|87 `lean/RetainedEnumeration.lean`|`de5dc56da9c55f864bcdf692be80ded05199f380b2acd9bda00135ed79cb828e`|
