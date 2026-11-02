# Context-specific witnesses for the 127 shared covers

## Result

All **543,827 selected box occurrences in 791 compatible contexts** now have an original-rule witness. The 127 class IDs and the selected geometry order within each class are preserved exactly from milestone 88. Each occurrence passed a direct interpretation of the checked `BoxWitness.lean` predicates and a second validation after reconstructing the deduplicated witness list.

The saved payload contains **4,387 distinct witness constructors**, **211 distinct aligned witness lists** and **141,625 stored list entries**. Its size is **313,081 compressed bytes**, with **1,208,365 uncompressed bytes**. The successful run took **5.234 seconds**, with no solver or Lean invocation and no changes to milestone 88 or earlier files.

This is a computational materialization and validity audit. The concrete witness equations have not been compiled in Lean by this task. It does not complete all-context coverage, row membership, column identities, charge interpretation or a global bound.

## Files and reproduction

Run `scripts/materialize_witnesses.py` with the saved Python runtime. The script has no external package dependency and locates the repository relative to its own path. It writes:

- `data/context-witnesses.json.gz`: the complete compact payload.
- `data/context-witnesses-audit.json`: counts, checks, input pins and generator hash.

The source common-cover payload is pinned to SHA-256 `c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93`. Its audit, all inherited input pins and the current witness-validity source are checked. All inputs are rehashed before success. The final compressed file is read back and compared with the complete in-memory payload. The run succeeded on its first attempt; there are no failure diagnostics for this task.

## Exact payload schema

All IDs and indices are zero-based.

| Field | Meaning |
| --- | --- |
| `box_catalogue[g]` | Six inclusive pairs [lower,upper], copied without renumbering from milestone 88. There are 2,637 geometry IDs. |
| `classes` | Rows `[class_id, geometry_ids]`, in the original class order 0..126. Each geometry list preserves the original selected-box order. Together these contain 82,659 class-box occurrences. |
| `witnesses[w]` | `[family_code, Lean_rule_index, offset, reverse]`. Reverse is 0 or 1. |
| `witness_lists[l]` | Witness IDs aligned position by position with the geometry list of the context's class. |
| `contexts` | Rows `[block_id, class_id, witness_list_id]`, preserving milestone 88's block order. Decode direction as `block_id // 75` and history as `block_id % 75`. |
| `rule_sources` | Reference catalogue/source indices, short-rule case numbers and source families, interval case numbers, and history signatures/digit positions. |
| `history_contexts` | The three contexts requiring history witnesses, including their positions in the aligned lists. |
| `input_sha256`, `script_sha256` | Exact input and source pins. |

Family codes map directly to the Lean constructors:

- `0`: `Witness.reference keyIndex offset reverse`.
- `1`: `Witness.short ruleIndex offset reverse`.
- `2`: `Witness.interval keyIndex offset reverse`.
- `3`: `Witness.history ruleIndex`, encoded `[3,ruleIndex,0,0]`; the final two zeros are placeholders.

Reference and interval offsets are count offsets whose direction pieces begin two positions later. Short-rule offsets are direction-window starts. Sum assignments are already represented by the box geometry, so the Lean witness constructor does not need to carry the assignment separately.

For any context row `[b,c,l]`, recover its complete ordered entries by pairing `box_catalogue[g]` with `witnesses[w]` for corresponding elements of `classes[c][1]` and `witness_lists[l]`. The current class IDs equal their positions, although consumers should use the explicitly stored ID when checking the format.

## Reconstruction and independent checks

The generator reconstructs all **573,640 original nonhistory box occurrences** from the source catalogues, using both orientations, all valid offsets and the explicit 1..5 sum assignments. For each required direction/geometry pair it chooses the lexicographically first available constructor tuple. This deterministic choice is made from the nonhistory occurrences before considering a history witness. Consequently a nonhistory witness is preferred whenever one is available, and its choice is independent of the history index.

Catalogue indices are verified against the actual Lean literal lists:

1. The 22 reference chunks and their picks agree with the ordered 1,378 union rows and source catalogue indices.
2. Short rules use the exact order `capRules ++ sumRules`, comprising 37 cap rules followed by three sum rules. The original milestone 48 ordering is not used as a Lean index.
3. The ten interval rows agree with `intervalKeys72` in order.
4. History rules have signatures [139,353,177], [460,350,180], [460,353,177] and digit indices 5,3,5.

Original occurrence construction uses oriented rule data. A separate validator reads the original un-reversed rule and reverses the actual candidate direction slice, then checks the interval endpoints and the appropriate Boolean validity conditions. In particular, short sums check the box's upper endpoints, require their sum to satisfy the cap and require every participating upper endpoint to be below six. Reference constraints require exact singleton bounds on the corresponding count slice. Interval and history checks preserve their original guards.

The direction table has 505 distinct entries, so the lookup index of each decoded table entry is its declared direction ID, as required by the history branch of `boxWitnessValid`. Each context is checked against its recorded source and target history compatibility. The context set, class assignments and geometry order agree with the pinned common-cover payload.

All 543,827 occurrences pass the independent validator, then all 543,827 pass again after reconstructing entries through the global witness and list IDs. The checks are computational interpretations of the Lean definitions; they are not an execution of the Lean kernel or a proof of Python/Lean implementation equivalence.

## Sharing measurements

| Measure | Count |
| --- | ---: |
| Selected class-box occurrences | 82,659 |
| Fully materialized context occurrences | 543,827 |
| Reference witness occurrences | 515,514 |
| Short witness occurrences | 23,625 |
| Interval witness occurrences | 4,685 |
| History witness occurrences | 3 |
| Unique witness constructors | 4,387 |
| Unique aligned lists | 211 |
| Stored aligned-list entries | 141,625 |
| History-free contexts | 788 |
| History-free unique lists | 208 |
| Distinct direction/class pairs | 507 |

Of the 211 lists, 147 are reused by multiple contexts and 126 are reused across multiple directions. The most widely reused exact list is shared by 33 contexts covering 15 directions. Identical list data does not itself transfer validity between different directions, since the direction-match conditions still depend on that direction.

All **543,824 nonhistory occurrences** use history-independent constructor choices. They reduce to **356,592 distinct (direction,geometry) pairs**, eliminating **187,232 repeated direction-only instances** if the checked history-transport interface is used after establishing the required base validity equations. The materializer checks consistency of the selected witness for every repeated pair. It does not compile those base equations.

Ignoring history constructors reduces the number of class-aligned list groups from **211 to 210**. Exactly one pair differs only in its history witness:

| Context | Class | Aligned list | History position | History rule |
| --- | ---: | ---: | ---: | ---: |
| direction 177, history 43 | 85 | 112 | 0 | 0 |
| direction 177, history 70 | 85 | 113 | 0 | 2 |
| direction 180, history 68 | 89 | 117 | 0 | 1 |

The first two rows have identical entries at every position after zero. Their only difference is the history constructor. The third history-bearing list belongs to a different class. Every history witness is at **position zero**, rather than at the end. This order must be preserved when checking a coverage tree whose leaf indices refer to the class order. A theorem that appends a history witness would require a corresponding ordering argument or adaptation to a leading history entry.

## Remaining certificate boundary

The output supplies the previously missing complete witness data for every context, with exact source indices and original geometry. The next checked stage must establish the concrete validity equations and combine them with the shared geometric certificates. The existing generic history-free transport theorem can support reuse across bounded histories of the same direction. Reusing a list across different directions requires the corresponding direction validity checks or a further justified transport result.

The data does not discharge the two reference refutation premises or establish concrete membership-diagram/row-array equality. Full-key indexing, endpoint columns, weights, pending local share targets and potential replay remain separate. No new numerical bound is asserted.

## Hashes

| Artifact | SHA-256 |
| --- | --- |
| Generator | `2373861008f56d4c5fc63e7e475aa44ed71941a1616e56b3352f79e04909f29b` |
| Compressed payload | `5dd985dc9e31441f481881895a827b7d88d68864b5104f07483adaaf86932d51` |
| Audit receipt | `1d4fe69968b3031759672992b5c1dc816642d88245564c4e9375623019ffd598` |

The uncompressed payload SHA-256 is `180af1361fe503ba1050cbeef2f1e5031bdc004f0dc7fb7e08d43999d0eae07c`. The receipt records all 47 pinned inputs.
