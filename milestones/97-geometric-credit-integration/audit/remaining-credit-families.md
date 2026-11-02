# Remaining credit families: bounded source audit

3 November 2026. Sources and successful receipts were inspected without compilation, solvers or background jobs. Only this note was written. This audit concerns the remaining six-transition credit families; the nine-direction geometric credit is being integrated separately. All conclusions about new wrappers below are proposals until checked in the current environment.

Completion update: the generic canonical and reversed symbol transfers,
including their encoded-suffix adapters, subsequently passed Lean in
`SymbolCredit97`. The geometric/history assembly also passed. The concrete
count-conditioned refutations and count-free profile still need integration.
The audit below records the source inspection that preceded those checks.

## Shortest credible route

1. Reuse the current `Snake9.LocalWindow.refuted_share_dir`, `Snake9.Guards79.actual_canonical_frame` and `actual_slice_decode` to add one generic **count-conditioned** canonical share wrapper. It is the share analogue of the existing `canonical_symbol_exclusion`.
2. Add its reverse using the already checked `dsOf_rev`, `symsOf_rev` and `coreShare_window_rev`. This supplies every orientation of the four forward rules and share120 without recreating their geometric normalizations.
3. Reuse the four old closed local refutations through uniquely named wrappers over their SAT/UNSAT modules. Avoid their legacy `ShareFrame` imports. The current environment already owns the duplicate declarations in `LocalWindowShareBridge`.
4. Reuse the checked combined catalogue from73 for the completed count-free rules and the full catalogue with its five explicit pending premises. Use the already checked75 suffix lookup to place their centres at $r+4,\ldots,r+8$.
5. Define each actual numeric lookup exactly as the builder does, prove each contribution bounded by the same five-centre share sum, then take their maximum with the geometric and history credits. No new local refutation or square-incidence proof is needed for these transfers.

## Four forward count-conditioned rules and reversals

The exact builder list is `70-proof-supported-share-model/scripts/build.py:15`; it uses the canonical last-six-direction word and the last five count symbols of the six-count code. The rules are:

| Direction word | Stored count symbols | Actual count bounds | Credit | Closed refutation namespace |
| --- | --- | --- | ---: | --- |
|012314|(3,3,3,6,5)|(3,3),(3,3),(3,3),(6,21),(5,5)|48|`Snake9.LocalWindow.SharePressure513`|
|012345|(3,6,2,3,6)|(3,3),(6,21),(2,2),(3,3),(6,21)|96|`Snake9.LocalWindow.SharePressure520`|
|012034|(6,3,6,3,3)|(6,21),(3,3),(6,21),(3,3),(3,3)|96|`Snake9.LocalWindow.ShareObstruction530`|
|012345|(4,6,2,3,6)|(4,4),(6,21),(2,2),(3,3),(6,21)|96|`Snake9.LocalWindow.ShareObstruction535`|

In each namespace, the exact theorem name is `refuted_share`, with statement

`RefutedShare window bounds resolution cap`.

The resolutions are12; the caps are47,95,95,95. The literal `window` is `winOf` of the displayed word, and `bounds` is `boundsOf` of its symbols. These finite equalities can be discharged while wrapping the old theorem.

Existing arbitrary-snake theorems in each namespace:

- `share_in_snake`: snake $p$, coordinate permutation $P$, start $t$, $t+6\le m$, six equations $P.\mathrm{fwd}(\operatorname{dir}(p,t+j))=c_j$, and the five displayed actual count intervals imply the displayed credit bound on $\sum_{i=0}^{4}\operatorname{coreShare}(12,p,t+i+1)$.
- `named_share_in_snake`: the same result using a duplicate-free list of named coordinates below9 and explicit repeated-coordinate direction word.

Sources:

- `51-exact-bucket-pressure/lean/SharePressure.lean`, `ShareInSnake.lean`, `LocalWindowCnf/SharePressure513.lean`.
- `52-share-on-235/lean/SharePressure.lean`, `ShareInSnake.lean`, `LocalWindowCnf/SharePressure520.lean`.
- `53-shares-on-sat-obstruction/lean/ShareBound0.lean`, `ShareInSnake0.lean`, `LocalWindowCnf/ShareObstruction530.lean`.
- `53-shares-on-sat-obstruction/lean/ShareBound5.lean`, `ShareInSnake5.lean`, `LocalWindowCnf/ShareObstruction535.lean`.

The three `data/verification.json` receipts report PASS, respectively26/59/203 built modules and14/12/19 axiom audits. This audit rehashed every recorded local source: all26,59,203 source hashes match, with no mismatch. These are historical successful proof closures, not a fresh combined import check.

### Import compatibility

The two old `SharePressure` modules and two old `ShareInSnake` modules have colliding module names despite distinct declaration namespaces. The old `ShareInSnake*` also imports `ShareFrame`, which declares `Snake9.LocalWindow.coreShare`, `refuted_share_bridge` and related constants already owned by the current `LocalWindowShareBridge`. Thus merely adding all old build paths and importing the arbitrary-snake wrappers is unsafe.

The least change is a uniquely named wrapper for each refutation using its unique `LocalWindowSat.SharePressure513`, `LocalWindowUnsat.SharePressure513` pair, and the analogous520/530/535 pairs. Apply `Snake9.LocalWindow.Tags.refutedShare_of_sat` to their existing `sat` and `unsat`. Alternatively port only the small `SharePressure`/`ShareBound*` root under a unique module name, preserving its namespace and proof text. Neither route needs `ShareFrame` or `ShareInSnake`.

These unique SAT/UNSAT modules are absent from the current95 first-resolved build paths. Their historical objects/support need to be made available with pinned provenance, then the new wrappers must be checked alongside `ConcreteRules95` and `DefinedProofGraph`. This audit does not establish that combined check.

### Exact numeric and directional transfer

For a graph edge at $r$, let $t=r+3$. Assume $r+9\le m$. Its five share centres are $t+1,\ldots,t+5=r+4,\ldots,r+8$.

Already checked helpers:

- `Snake9.Direction77.direction_decode` in77 `lean/ActualDirectionIds.lean`: the stored nine-direction word at `directionId p r` is `canon (dsOf p r 9)`.
- `Snake9.GraphInterpretation74.canonical_nine_share_suffix` in74 `lean/WindowStateShift.lean`: canonicalizing its last six directions gives `canon (dsOf p (r+3) 6)`.
- `Snake9.Guards79.actual_slice_decode` in79 `lean/ReferenceRetention.lean`: instantiate $s=1,w=5$ to obtain
  `sixCode p r % 7776 = encodeCounts syms 0` implies `symsOf p (r+3) 6 = syms`, for a five-entry list with symbols in1..6.
- `Snake9.Guards79.actual_canonical_frame` in79 `lean/CanonicalExclusions.lean` supplies the coordinate realization of any fitting actual canonical word.
- `Snake9.LocalWindow.refuted_share_dir` in current `LocalWindowShareBridge.lean:239` takes a `RefutedShare (winOf cs) (boundsOf syms) M K`, the coordinate frame, and exact symbol matches; it concludes $K+1$ is at most the corresponding share sum. Its internal `boundOf_symC` and `coreAlpha_le_21` already preserve saturation correctly.

A proposed generic wrapper should assume a canonical match, `symsOf p t 6 = syms`, and the closed refutation. The existing `canonical_symbol_exclusion` is an almost literal template: replace `Refuted`/`refuted_dir` and conclusion `False` by `RefutedShare`/`refuted_share_dir` and the share conclusion. The conclusion can use `List.range syms.length`, then simplify a five-symbol instance.

For reversal, use $\operatorname{revSnake}(p)$ at $m-t-6$ with both `canon (dsOf p t 6).reverse = cs` and `(symsOf p t 6).reverse = syms`. Existing `dsOf_rev`, `symsOf_rev`, and `coreShare_window_rev 12 p t 5` transport these conditions and the unchanged five-centre sum. This orientation-sensitive count handling is essential: using only `graphShape` and leaving the counts in forward order would be incorrect.

The builder's reversal is `canon(word.reverse)` paired with `syms.reverse`. For012314 its canonical reversal is again012314; for012034 it is012342; the distinct-direction word stays012345. A generic equivalence `canon ds = canon cs.reverse` with canonical `cs` implies `canon ds.reverse = cs` follows from `reverse_canon` and canonical idempotence. It can also be discharged separately for the four finite patterns.

## Share120

Source: `72-four-count-proof-closure/critical-charge/share-proof/lean/Share120/Refuted.lean` and `Geometry.lean`.

Exact names:

- `Snake9.LocalWindow.ShareWindow120.refuted : RefutedShare window bounds resolution cap`.
- `Snake9.LocalWindow.ShareWindow120.share_bound` for six distinct named directions, with the five bounds `(4,4),(5,5),(4,4),(2,2),(6,21)`, concludes
  $120\le\sum_{i=0}^{4}\operatorname{coreShare}(12,p,t+i+1)$.

The literal word is012345, resolution12, cap119. The builder in `72-four-count-proof-closure/critical-current/scripts/prepare.py` accepts count symbols `(4,5,4,2,6)` or `(6,2,4,5,4)` when its last six directions are distinct. It raises the common share credit to at least120 by maximum.

The receipt `critical-charge/share-proof/data/proof-audit.json` is `PASS_LOCAL_SHARE_THEOREM`:99 modules,72 axiom audits. All99 recorded sources match their receipt hashes in this audit. The final named-coordinate theorem is checked; the inspected `Share120` source directory has no separate reversed theorem. Its use in both graph orientations therefore still needs the generic reverse transfer above. No new certificate is required.

The generic count-conditioned wrapper can use `ShareWindow120.refuted` directly. Alternatively use the named theorem after recovering six distinct coordinate names, but this duplicates normalization already available from `actual_canonical_frame`.

The share120 and current share12 copies of `LocalWindowShareBridge.lean`, plus73's adapter copy, are byte-identical: SHA-256 `8b2d06a67664f7d9ded4d0b3422e8cf73c151caed2a0cc08772ec74cf7d59ca8`. Share120's named modules are absent from the current95 build path;73's successful combined overlay includes them and shares its declarations safely with the count-free proofs.

## Completed and full count-free catalogues

### Checked local statements

`73-countfree-share-catalogue/lean/CombinedCatalogue.lean` contains:

- `Snake9.CatalogueIntegration73.canonical7300`, shape012031, credit16.
- `Snake9.CatalogueIntegration73.canonical7304`, shape012304, credit16.
- `Snake9.CatalogueIntegration73.canonical7305`, shape012310, credit12.
- `Snake9.CatalogueIntegration73.canonical7306`, shape012314, credit16.

Each takes a fitting six-transition window and either its forward or reversed canonical match, with no count hypotheses. Each concludes a bound on its five internal shares. Each is closed using `Snake9.LocalWindow.ShareWindow730X.refuted`; the respective `Share730X.Reversal` modules contain checked `share_bound_rev` theorems too.

The fifth completed shape012345 has weaker credit12 from `Snake9.LocalWindow.ShareWindow12.refuted` / `.share_bound`, in `72-four-count-proof-closure/critical-current/share-proof/lean/Share12/`. Its broad count bounds are `(0,21)` at all five positions. The generic `CountFreeAdapter73.share_bound_of_either_canonical_match` can apply this refutation with cap11 and either orientation. It does not prove the proposed credit16.

The completed-profile lookup is therefore16 on012031,012304,012314;12 on012310,012345; and0 on the other four representative shapes. This is a profile of **added** floors; other geometric/count-conditioned credits remain in the maximum. No currently checked unconditional theorem gives a minimum share12 for every shape. `catalogue_share_ge12` retains the full local premises.

### Full target and exact remaining premises

`Snake9.CatalogueIntegration73.partial_catalogue_share` is checked and retains precisely:

- `RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15` (7301),
- `RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 19` (7302),
- `RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15` (7303),
- `RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15` (7307),
- `RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15` (7308).

Here `broadBounds = List.replicate 5 (0,21)`. With these premises, a snake and $t+6\le m$, it proves `windowLower p t` bounds the five-centre sum. The four completed target cases are supplied within its proof. The full profile is16 on seven shapes,20 on012034, and12 on012310.

`Snake9.CountFreeAdapter73.catalogue_share_bound` and `Snake9.GraphInterpretation75.graph_catalogue_share_bound` each retain all nine certificate arguments. Do not mistake their existence for discharged catalogue premises. To avoid re-proving selection, instantiate the four completed arguments, leaving the five above explicit; or use `partial_catalogue_share` at $t=r+3$ and rewrite via `actual_suffix_lookup`.

### Actual graph lookup

`75-exact-history-bridge/lookup/lean/GraphShareLookup.lean` already proves:

- `graphShape_eq_selectedShape` on every induced six-direction word;
- `actual_suffix_lookup`: the builder's lexicographically smaller canonical orientation of the nine-word suffix equals the catalogue's selected shape of `dsOf p (r+3) 6`;
- `graph_catalogue_share_bound`: selected full floor bounds `((List.range 5).map fun i => coreShare 12 p (r+i+4)).sum`, under all nine premises.

The full conditional bridge needs only the four-premise substitution and stored-direction decoding. For the completed profile, define its literal finite floor table and split its five positive branches; `selectedShape_mem_and_match`, the four `canonical730X` theorems and the share12 generic canonical adapter prove each branch. The default zero is immediate. Use `actual_suffix_lookup` to connect this table to the exact graph key. This small completed-profile assembly has not yet been checked here.

### Imports and receipts

`CombinedCatalogue.lean` imports `Share120.Geometry`, `Share12.Geometry`, `FiveCentreOverlap`, `CountFreeTarget`, `SixShapeCoverage`, `CanonicalShareAdapter`, `ConditionalCatalogueDispatch`, and the four completed `Share730X.Reversal` modules. Its receipt `73/data/integration-audit.json` reports `PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET`,35 standard-axiom audits, and verifies the exact five remaining theorem parameters.

`73/build/CombinedCatalogue.olean` and `73/build/combined/` hold the checked integration and its merged objects. The existing95 receipt does not include these roots. A read-only comparison found224 common modules between73's `overlay_objects` receipt and95's first-resolved paths; **all224 object hashes are identical**. This is strong evidence that the overlay can be reused. A new combined import/check with `ConcreteRules95` and `DefinedProofGraph` is still required before claiming coexistence.

The75 lookup receipt is `PASS_EXACT_GRAPH_SHARE_LOOKUP`, eight audited declarations. Its modules already occur in the current95 environment. The adapter's receipt is `PASS_CONDITIONAL_CATALOGUE_DISPATCH`; this status refers to checked conditional statements.

## Receipt pins and limits

SHA-256 of inspected receipts:

| Receipt | SHA-256 |
| --- | --- |
|51 `data/verification.json`|`5a8b07eeb9fd8cafd8da8faea4fbb1a5c677b84933d6039ce82c356308e1669d`|
|52 `data/verification.json`|`271bafc176b112250f0c64d0ce03d52abd01f08d621dd6d473ba9e22bd963e5b`|
|53 `data/verification.json`|`1146f0edf57ac2a2c853b99271da6460d5febe31d0d0063657da3cb49b4d1ffa`|
|72 share120 `data/proof-audit.json`|`aa02ec872bc8d1742d095c5119df41effe1a99051d2bbc7d7dd74d7ad004dfaa`|
|72 share12 `data/proof-audit.json`|`a7e4339fe3152c30e11f009740a7fd38c63cdef204b7f0102f66acdedda836f8`|
|73 `data/integration-audit.json`|`d90a4c77464c10db1d62a8b70cb7f14bb15fac5162ca01255128fd727d5d1d01`|
|75 lookup `data/proof-audit.json`|`08d40929a73eacb66551e311eb271ef6fc524a5f882faef6c0c209b9f68689ad`|

The share12 audit also has221 matching local source hashes. Cases7300,7304,7305,7306 each have a final `PASS_LOCAL_SHARE_THEOREM` receipt; the other five cases have no such final receipt at inspection.

The new generic count-conditioned adapter, reversed numeric dispatch, completed-floor evaluator and combined weight evaluator are proposed implementations, not checked results of this read-only audit. The existing semantic/certificate theorems are checked at the scopes stated above. Their integration alone does not supply graph coverage, a full potential certificate or a numerical improvement to235.
