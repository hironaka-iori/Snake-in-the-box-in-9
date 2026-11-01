# Exact history-graph interpretation audit

The current graph has **five truncated count symbols per state and six per edge**. The existing contributor seven-centre chain has six per state and seven per edge. Its normalization and summation proofs provide reusable arguments, but its table bundle is not an instance of the current share/history graph.

This audit is pinned to contributor commit `cd0c90fddf12170d735ee34fcc501e99c60632a6`. Exact snapshots and hashes are in [data/contributor-sources.json](data/contributor-sources.json). Current source hashes, declarations, graph metadata and inherited proof receipts are in [data/interface-audit.json](data/interface-audit.json). Read-only Git extraction was used; no Git state was changed. The separately owned `optimization/` folder is outside this audit's scope.

## Exact current model

The audited source is `milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json`: 1,601,856 states and 4,947,008 edges. The conditional comparison `countfree16-all-except012034x20-except012310x12` changes weights and retains the same endpoints, direction IDs, count codes and history IDs. Its saved Python verification reports mean 496 and potential range 600. Neither this metadata audit nor that Python receipt is a complete Lean graph certificate.

Let `d_j` be the actual transition directions, `alpha_j = coreAlpha p j`, and `b_j = min(6,alpha_j)`. For edge start `r < m-8`:

| Component | Exact meaning |
| --- | --- |
| Edge direction shape | `canon [d_r,...,d_(r+8)]`, one of 505 nine-direction words |
| Source direction shape | `canon [d_r,...,d_(r+7)]`, one of 132 eight-direction words |
| Target direction shape | `canon [d_(r+1),...,d_(r+8)]` |
| Edge count symbols | `[b_(r+3),...,b_(r+8)]` |
| Source count symbols | First five, `[b_(r+3),...,b_(r+7)]` |
| Target count symbols | Last five, `[b_(r+4),...,b_(r+8)]` |
| Entering count | `b_(r+8)` |
| Charged share centres | `r+4,...,r+8` |
| Count-free suffix | Six transitions starting at `r+3` |

Counts are encoded in base 6 using digits `b_j-1`. Write `B = 6^5 = 7776` and `N = 132*B = 1026432`. The prefix-history list has 75 entries: the empty prefix, 31 one-symbol prefixes, and 43 two-symbol prefixes. Thus the total state count is `N + 74*B`.

For a six-count code `c`, source/target shape indices `s,t`, current history `q` and next history `q'`, the builder stores:

```
U = (s*B if q=0 else N+(q-1)*B) + c//6
V = (t*B if q'=0 else N+(q'-1)*B) + c%B
weight = 120*(c%6+1) + credit
```

The longest listed suffix of `prefix[q] ++ [directionId]` determines `q'`. A nonempty history class restricts the source direction shape to the recorded compatible shape. The actual walk must begin with `q_0=0`; arbitrary history initializations are not justified.

Authoritative construction sources:

- [milestone70 builder](../70-proof-supported-share-model/scripts/build.py): base exclusion tables, shorter local restrictions, geometric/count-specific shares, history transition, rejection and numeric state encoding.
- [milestone72 filter](../72-four-count-proof-closure/scripts/graph.py): ten checked four-count interval exclusions. Its independent [verifier](../72-four-count-proof-closure/scripts/verify_graph.py) distinguishes the lower and upper endpoints of symbol 6.
- [current preparation](../72-four-count-proof-closure/critical-current/scripts/prepare.py): the checked count-specific share-120 update.
- [count-free comparison](../72-four-count-proof-closure/critical-current/scripts/countfree_effect.py): maximum with the new shape-dependent share floor.

The stored history rules comprise 55 share rules and three exclusion rules. Their count caps are 1, 2 or 5, all below the saturated symbol 6. The short sum restrictions also explicitly require every participating symbol to be below 6. These source checks avoid interpreting the symbol 6 as an exact count; the corresponding Lean guard-to-hypothesis bridge remains to be assembled.

## Existing reusable proofs

| Obligation | Existing declaration and evidence | Reuse limit |
| --- | --- | --- |
| Actual induced direction block | `WindowAutomatonBridge.snake_inducedPattern_block`; `DirectionWindow.pathDir_eq_dir` | General length, including 9 and 11. Existing compiled support was hash checked for the new small module. |
| Canonicalization | `WindowAutomaton.canon_isRGS`, `length_canon`, `inducedPattern_canon`, `canon_canon_take`, `canon_canon_drop`, `canon_canon_drop_reverse` | Symbolic normalization, independent of graph state numbering. |
| Truncation | `WindowAutomaton.sym_ge_one`, `sym_le_six`, `sym_le`; `LocalWindow.boundOf_symC`, `coreAlpha_le_21` | Symbol 6 means `[6,21]`. `sym` and `symC` have identical definitions. The exact base-6 code and interval guards still need their numerical representation lemma. |
| Canonical exclusion transport | Contributor `DirectionWindow6.window_refute6` / `no_forb_window6`, `DirectionWindow7.window_refute7`, `no_forb_H9`, `direction_windows_core7` | Generic arguments take `AllRefutedList`, key validity and coverage hypotheses. Their exact key tables and first/last count offsets differ from the current graph. |
| Small-table lookup coverage | Contributor `Cover6`, `Cover7`, `CoverH`, `cover6_spec`, `cover7_spec`, `coverH_spec`, `encB_inj` | Useful method for connecting finite codes to certificates. No existing theorem identifies these tables with the current 1,378 reference keys plus added guards. |
| Nine-transition geometric credit | [ExtendedShare59.credit_in_snake](../59-extended-share-window/lean/ExtendedShareBridge.lean); the 357 positive geometry instances | Source hashes match the successful milestone59 receipt. These already conclude the sum over centres `r+4,...,r+8`, with an explicit coordinate permutation. |
| Eleven-transition geometric credit | Milestone61 and milestone67 `in_snake` declarations, e.g. [FamilyCharge67.G000.in_snake](../67-critical-family-charge/lean/ChargeBatch00.lean) | Centres at offsets 6 through 10 become the required `r+4,...,r+8` for a window beginning at `r-2`. Requires proof of history occurrence and coverage of every compatible word. |
| Count-free share lookup | [CountFreeAdapter73.catalogue_share_bound](../73-countfree-share-catalogue/adapter/lean/ConditionalCatalogueDispatch.lean) | Checked conditional theorem, with all nine certificate premises explicit. Also connect its forward-if-listed representative to the builder's minimum of forward/reversed canonical words; this is a small finite identity, not a global graph theorem. |
| Local-to-global share quantity | Contributor `ShareBridge.shareN_eq_coreShare`, `core_charge_sum_le`; checked local [CountFreeBridge.core_share12_charge_le](../73-countfree-share-catalogue/bridge/lean/CoreShareBudget.lean) | Gives `24*T + sum(coreShare12) + 840*(m+1) <= 221136` for `m>=1`. This part is available. |
| Five-centre overlap | [ExtendedBudget59.window_budget](../59-extended-share-window/lean/ExtendedBudget.lean) | Instantiate `J=range(m-8)`, `N=m+1`, `offset=4` and the actual per-edge credit inequality. |
| Omitted singleton budget | [BoundaryCharge67.discarded_counts](../67-critical-family-charge/lean/BoundaryCharge.lean), `aggregate_charge`, `global_charge` | The omitted indices `0,...,7,m` contribute at least 21. This gives `W+4200*m <= 1098960` after the actual weight definition is supplied. |
| Potential telescope | [CriticalFamily61.path_bound](../61-critical-family-share/lean/FinitePotential.lean) | General open walks; no closed-cycle assumption is needed. Supply every actual step inequality and the potential range. |
| Finite potential table check | `CriticalFamily61.checkEdges`, `edge_of_check`; contributor `StepOK7`, `step7_raw`, `invariant7` | General methods exist. The current complete 4,947,008-edge potential table has a Python receipt, without a Lean replay in the inspected sources. |

The source/hash checks of the milestone59, milestone61 and milestone67 receipts are saved in `interface-audit.json`. No new full rebuild of those inherited proofs was performed.

## Contributor UpperBound234 comparison

The pinned [UpperBound234](upstream/UpperBound234.lean) assembles `allRefuted7B234` and invokes `upper_234_of_refuted7B234`. Its count-only potential has slope `6423/1544`, a 13-bit range bound, six counts per state, and no empty-square or prefix-history component. `WindowAutomaton7Defs.step7_raw`, `own7_false`, `invariant7`, and `total_bound7` expose the useful generic decomposition: rule out local exclusion hits, apply a checked finite step table, telescope, and add boundary counts.

The pinned [contributor README](upstream/Contributor-k7-README.md) reports that its B234 composition used temporary proof stubs for the 792 production shards and the new K7 certificates. It separately reports successful generic framework/coverage checks. The present audit does not verify a complete contributor bound 234 and does not import any of those temporary objects. A theorem's source name alone is insufficient evidence that its complete dependency chain has been checked.

## Small checked addition

[WindowStateShift.lean](lean/WindowStateShift.lean) adds four proved identities:

- `dsOf_slice`: taking a subwindow of a valid direction block equals the corresponding shifted `dsOf` block.
- `canonical_nine_source`: the recanonicalized first eight directions equal the actual source-state shape.
- `canonical_nine_target`: the recanonicalized last eight directions equal the actual next-state shape.
- `canonical_nine_share_suffix`: the recanonicalized last six directions equal the window beginning at `r+3`.

Lean 4.19.0 checked all four in 16.109 seconds. [data/proof-audit.json](data/proof-audit.json) records `PASS_WINDOW_STATE_SHIFT` and the source, object, log and support-receipt hashes. Printed axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`. Run `scripts/check_small.py` to reproduce this small check using the hash-matched inherited support.

The separate [PotentialRangeObstruction.lean](lean/PotentialRangeObstruction.lean) proves the rational algebra: if `L<=227`, `p<=496`, `p*L-W<=R` and `632<=496*L-W`, then `227*p-R<=111960`. It was checked in 9.094 seconds with standard axioms; [data/potential-obstruction-proof.json](data/potential-obstruction-proof.json) records the hashes and check. Reproduce with `scripts/check_small.py PotentialRangeObstruction`. This lemma assumes the cycle/path inequalities.

The [short-walk optimization tests](optimization/README.md) now supply exact graph witnesses for six specified weakenings of the mixed share catalogue. Each retains a cycle of mean496 and has a walk of length7 through17 with deficit at least632. Direct array and witness checks passed separately from discovery. Consequently, changing the constant slope or potential cannot recover the conditional234 arithmetic for those weakened graphs under the existing boundary budget. The witness membership checks are in Python; the general obstruction algebra is Lean-checked. No arbitrary-snake realization or improved global bound is inferred.

## Smallest remaining graph interface

The useful next theorem should construct an actual walk, rather than assume that the snake is represented. For `p : Snake m`, `m>=9`, set `n=m-8`. Define each canonical nine-direction ID and each six-count code from the actual snake; define `q_0=0` and advance the recorded prefix automaton. A precise target is:

```
There exist state : Fin (n+1) -> Fin 1601856
and edge : Fin n -> Fin 4947008 such that, for every r<n:
  U[edge r] = state r
  V[edge r] = state (r+1)
  direction[edge r] = the actual canonical nine-direction ID
  count_code[edge r] = the actual six truncated-count code
  history[edge r] = q_r
  weight[edge r] <= 120*min(6,alpha_(r+8))
                   + sum(i=0..4, coreShare12(p,r+i+4)).
```

This is an interface specification, not a declared theorem. The source and target direction equalities are now checked. To implement it, the remaining semantic tasks are:

1. Encode the 132 source shapes, 505 extensions, five-count state blocks and six-count edge blocks, preserving prefix/suffix numbering.
2. Prove that `prefix[q_r]` is the longest listed suffix of the already-read actual direction IDs. Then an emitted three-ID signature refers to the actual overlapping nine-direction windows, starting at `r-2`. At `r=0,1`, no three-window history credit may be emitted.
3. Dispatch every current exclusion guard to its exact local theorem. Include interval saturation, reversal, short sum rules and all three history exclusions. A generic `AllRefutedList` theorem helps, but does not supply the current exact catalogue coverage automatically.
4. For each emitted history signature, prove that the actual eleven-direction word belongs to the complete compatible-variant list. The builder takes the minimum bound over all variants; each variant must supply its own checked bound. Three canonical nine-window IDs can have multiple eleven-word realizations.
5. Prove each applicable geometric, count-specific and count-free credit is below the same five-centre share sum. Their maximum is then below that sum. Do not sum overlapping credits.

Independently, bind the precise finite data to Lean and prove the full per-edge potential inequality and range, using the existing `checkEdges` interface or a compressed equivalent. The Python graph hashes and potential checks do not discharge this kernel-checking obligation.

Once those two gates are complete, `path_bound`, `window_budget`, `discarded_counts` and `core_share12_charge_le` supply the global accounting. No replacement square-counting theory is required. This audit establishes no new numerical bound and does not resolve the exact optimum.
