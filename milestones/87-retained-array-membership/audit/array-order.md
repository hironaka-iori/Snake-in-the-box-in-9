# Saved retained-array order and endpoint audit

## Result and scope

The source-derived order is strictly lexicographic in `(direction, history, count_code)`. All 4,947,008 saved rows satisfy this order, with zero duplicate keys. All 37,875 possible direction/history block positions were counted: 791 are compatible and nonempty; 37,084 are incompatible and empty. Compatible blocks contain between 3,165 and 8,389 rows. Every saved source and target endpoint matches the builder formula. A block prefix offset plus the rank of a stored accepted code therefore identifies every stored edge uniquely.

Endpoint pairs are not unique: there are 4,740,419 distinct `(U,V)` pairs and 206,589 pairs of multiplicity two, with maximum multiplicity two. The full candidate key or edge-array index must remain the edge identity. An assembly that treats `(U,V)` alone as its key would identify distinct edges.

This audit reads existing sources and arrays without rerunning a historical builder, solver or Lean compiler. The initial ordering check was followed by the separately authorized independent retention comparison below: exact accepted-code equality now holds computationally for every compatible block. Its Lean finite-array coverage certificate remains outstanding; exact equality is a sufficient stronger certificate. No missing retention-filter family was found in the inspected source chain. The metadata/source hashes and all per-block counts are saved in `data/array-order-audit.json`.

## Exact files and provenance

The structural array used by the current comparison is:

`milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz`

Its metadata is:

`milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json`.

The source chain is:

1. `70-proof-supported-share-model/scripts/build.py --enriched` writes 4,997,518 rows to `70-proof-supported-share-model/build/enriched-graph.npz`, with metadata `data/enriched-model.json`.
2. `72-four-count-proof-closure/scripts/graph.py --proved-only` applies ten interval cases and retains the stable subsequence of 4,947,008 rows in `72-four-count-proof-closure/build/proved-graph.npz`. It removes 50,510 rows. The individual case-removal counts overlap and cannot be added to obtain this total.
3. `72-four-count-proof-closure/critical-current/scripts/prepare.py` writes `source-graph.npz`. It raises only the weight column on 1,280 rows for the checked share-120 rule. All structural columns and their order remain identical to the preceding graph.
4. `73-countfree-share-catalogue/data/proved-model.json` records the same structural source hashes for the current completed-share comparison. Its weight SHA differs because additional share floors change weights; there is no structural edge change in that metadata.

The `source_arrays_sha256` field in `critical-current/data/source-proved-model.json` was reset by `critical-current/scripts/prepare.py` to the ten-case graph hashes. It is therefore not the original 4,997,518-row enriched graph's hash table, although inherited `candidate_edges` and `removed` fields still refer to that preceding filtering stage. The audit checked each link against its correct predecessor.

All six arrays of all three saved graph archives were read sequentially and their raw hashes checked against their respective metadata. They are one-dimensional signed 32-bit arrays. No six-array graph dictionary was retained in memory. The reported current structural arrays agree with the current completed-model metadata.

## Ordering derived from source

The ordered direction table has 505 entries in `59-extended-share-window/extended/data/model.json`; its eight-direction shape table has 132 entries. The 75 ordered history prefixes and compatibility labels come from `67-critical-family-charge/data/full-model.json`. These lists agree exactly with the copies saved in the enriched model.

In builder 70:

- Line 32 creates count codes in increasing order, `0..46655`, and decodes the six base-six digits, adding one to obtain symbols `1..6`.
- Line 34 iterates the 505 direction IDs in table order.
- Lines 36–53 form a count-only mask for that direction; line 54 uses `flatnonzero`, preserving increasing code order.
- Line 58 iterates history IDs `0..74`. Line 59 skips incompatible nonempty histories.
- Lines 62–69 apply the history-dependent rejection mask as another stable selection.
- Line 70 appends each block; line 71 concatenates in append order.

In graph 72, line 36 applies `v[keep]` to every column. This stable subsequence preserves the previous key order. The subsequent share-120 preparation changes only weights.

Let the block index be

\[
 b(d,q)=75d+q,
 \qquad 0\le d<505,\quad 0\le q<75.
\]

All 37,875 block positions are represented in the audit receipt, including empty incompatible positions. There are 791 compatible blocks, hence 36,904,896 compatible candidate keys before count rejections; this is distinct from both the 4,947,008 stored edges and the 23,561,280 direction/count pairs used in isolated filter comparisons.

## Endpoint and history formulas

Set

\[
 B=6^5=7776,\quad N=132B=1026432,\quad S=N+74B=1601856.
\]

For the nine-direction table entry `ds`, let `ps` and `ts` be the table IDs of the canonical first and last eight directions. The source block is allowed exactly when `q=0` or `compatible_shapes[q]=ps`.

Append `d` to the stored prefix at `q`. Among all nonempty listed suffixes, `nq` is the first maximum-length choice in list order; it is zero if there is no nonempty listed suffix. The source's `max(..., key=length)` selects this. The dictionary is unique, and suffixes of a fixed length are unique, so there is no competing same-length suffix. For every one of the 791 compatible blocks, the computed target history is either zero or compatible with `ts`; the builder's assertion fails on none of them.

For a retained code `c`, builder 70 line 70 gives

\[
 U(d,q,c)=
 \begin{cases}
 psB+\lfloor c/6\rfloor,&q=0,\\
 N+(q-1)B+\lfloor c/6\rfloor,&q>0,
 \end{cases}
\]

\[
 V(d,q,c)=
 \begin{cases}
 tsB+(c\bmod B),&nq=0,\\
 N+(nq-1)B+(c\bmod B),&nq>0.
 \end{cases}
\]

These formulas were checked directly against every stored `U` and every stored `V`, with zero mismatches. The count code is bounded by 46655; both endpoint codes are below 1601856.

## Complete retention-filter inventory

The following tests are the only exclusions in the inspected structural source chain.

1. **Source history/shape compatibility:** skip a nonzero history whose compatible shape differs from `ps`. The target compatibility is an assertion, not another row-deletion mask; its validity was checked for every allowed block.
2. **Reference union:** builder 70 lines 22–39 take 1,378 joint-reversal canonical keys from the 235 and 236 catalogues. Both orientations are entered in the lookup tables. For width `w=2..6` and offset `s=0..6-w`, the direction piece is `ds[s+2:s+w+3]`, and the encoded count slice is `floor(c/6^(6-s-w)) mod 6^w`. Matching a reference code rejects the candidate. All intervals in the 235 input are exact symbols 1–5 or [6,21], so extracting the lower endpoints yields the intended symbols. The closed-refutation premises remain distinct from this table inspection.
3. **Forty enriched short rules:** current case files from milestones 47, 48 and 49, plus explicit case 501, match the saved rows exactly. For length `L`, the source tests offsets `0..9-L` in both orientations. A local position `j` maps to `offset+j` forward and `offset+L-j` reversed. It applies a rule only when every tested position lies in 3..8, then accesses count column `position-3`. The milestone 47 singleton tests reject equality to one. Other cap tests reject when every tested value is at most its listed cap. The three sum tests reject a sum at most the cap only when all participating symbols are below six: case 481 cap 4 at positions [1,5]; case 482 cap 5 at [4,7]; case 501 cap 12 at [1,4,5]. Removing these unsaturated guards would change the retention predicate.
4. **Three remembered-history exclusions:** after appending the current direction ID, a signature match requires at least three identifiers and exact equality of the last three. Only `mode='exclusion'` changes acceptance. The active `(direction,history)` blocks are `(177,43)` for signature `(139,353,177)` and sixth-symbol cap 2; `(180,68)` for `(460,350,180)` and fourth-symbol cap 2; `(177,70)` for `(460,353,177)` and sixth-symbol cap 2. The other 55 pattern rows modify shares only.
5. **Ten proved-only interval exclusions:** cases 7202, 7203, 7206, 7211, 7212, 7215, 7216, 7217, 7218 and 7219. Graph 72 tests direction offsets 2, 3 and 4, both orientations, each five-direction piece and its four internal counts. The count index is `offset+j-3` forward or `offset+5-j-3` reversed for `j=1..4`. Matching all four stored intervals rejects the row. Every upper endpoint is below six or is 21, as required for symbol-six interpretation. The saved applied cases are all present in the completed-case audit.

Geometric base shares, the four forward share rules and their reversals, all share-mode history rows, share120 and later count-independent share floors modify only weights. There is no reachability pruning, strongly connected component pruning, potential threshold, endpoint-pair deduplication or hidden sorting step in the inspected retention chain.

## Rank indexing and the remaining checked assembly

Let `A_b` be the strictly increasing list of count codes actually saved in block `b`, let `n_b=|A_b|`, and set

\[
 O_b=\sum_{t<b}n_t.
\]

For every saved code `c` in that block, its unique edge-array index is

\[
 e=O_b+\bigl|\{t\in A_b:t<c\}\bigr|.
\]

All per-block offsets and ranks were checked; the last offset is 4,947,008. `data/array-order-audit.json` stores all 37,875 counts, all 37,876 offsets, each first/last saved code and the next-history table.

For the Lean actual-snake assembly, the missing implication is stronger than saved-array sortedness. The independent checker below establishes the corresponding finite equality computationally, while the Lean connection remains to be proved. One must connect the canonical direction ID, history update and six count digits from the checked actual state sequence to the exact builder acceptance predicate, and establish for every compatible block that every accepted code belongs to `A_b`. Exact equality, as computed here, is a sufficient stronger result. This includes all five exclusion families above and their precise offsets and saturation guards. Under that one-sided coverage, the existing actual-snake retention theorems produce membership in `A_b`; the rank formula then supplies an in-bounds edge index with the required key, endpoints and neighbouring state agreement.

The two reference-catalogue premises must remain explicit until the closed reference dependencies are supplied. Python hashes and direct finite array comparisons are evidence about saved bytes, not Lean proofs of the finite tables or their source-level extensional equality. A checked regeneration/table certificate, or an equivalent finite-membership construction tied to those arrays, is still required. Edge-weight interpretation, all compatible eleven-direction realizations and the potential proof remain separate obligations after structural membership. No global upper-bound claim follows from this audit.

## Hashes

| Artifact | SHA-256 |
| --- | --- |
| Builder 70 source | `bffe9f3d541a807841d564a85bc3f5d2523ae73ee7b8218b79facdac9a4987db` |
| Graph 72 filter source | `7818a248e26135990ba4ffee2a57e7619376ee35517ef8c856aec3853ea5912c` |
| Current-source preparation | `3dcaa916b1c3f9920acbe5876464fa63e665ba1a93c5ce4c6f949a4a204b2709` |
| Current-source metadata | `b667dade57b02849a3169c521c95dc3e5e9ce394101ad82d4cb55ee5c893c821` |
| Ordered direction tables | `2334325d650cc9b71c0c6ab836183cecd4f1fc4d8b6555f63211592a22a0e2bf` |
| History and pattern tables | `08fc18347eff9065d873cb8be01b4b72129e1ee939b4bf1474d04640cc8bc274` |
| Current source NPZ | `b40f1ca44ad8f3269f890efe8decc60f19dabd647f11255c05df3727341c2c34` |
| Current raw array `U` | `e910280dc3ad25c32010127c7af2f7d837a162e1095a4aa85fdd0f996b08f46d` |
| Current raw array `V` | `21956ceeb6414238baae68543ac9677c791c07575deeb2664facdf6490374f94` |
| Current raw array `weight` | `acd19583f5de41d789206d369e37493228e8b8b85708db2427781f0d6766b5d4` |
| Current raw array `direction` | `e0e598fa564c6474be6ef98215886248bfca188f3eb47c59b2d9e96ea20b8705` |
| Current raw array `count_code` | `1917e3700ccdee418c22f29829b309775f9212f026e55e394038c1ddfa25210e` |
| Current raw array `history` | `23eb7524f277153fc0ca23ce4cdf005e28c8091f7993b44bfa34812a5adb57d7` |
| Current reproducible array-order audit receipt | `e3096ad1e30227d992ab5c4fd926a114208455a1eb71b1c353c1ea05bb8c4cdf` |
| Archived original array-order receipt | `f5db16e24474e7eaceecc1742d8c7acf3edb5f72c0402b7bf8de6be1e5433d8a` |

The JSON receipt also pins the earlier graph archives, all filter input files and current model metadata. No pre-existing research artifact or saved graph was modified. The initial audit wrote this report and its JSON receipt; the separately authorized extension added the independent checker and its receipt.

## Independent exact retention comparison

The bounded extension is saved as `scripts/check_arrays.py`, SHA-256 `68a9c7950062cd8f4f8d942996b61a4e92867b5e5c68f61d815ef87d64367b34`. It ran successfully with exit code zero in 4.109 seconds and wrote `data/retention-equality.json`, SHA-256 `9605355e849a501cf77997bc005e9a974dd9b66f3ae54bdd4aecbdfe01f4026f`. No earlier builder was executed, no weights were calculated and no solver or Lean process was launched.

The checker reconstructs the complete acceptance predicate from the original reference inputs, the current short-rule case files plus explicit case 501, the three history exclusions, the ten applied interval cases and the ordered direction/history tables. Every input is hashed when read and rehashed before the success receipt is written. The checker source itself is pinned in the receipt. The current short rows are also compared exactly with the saved enriched model.

Its implementation differs from the historical source in several directly relevant ways:

- It expands both orientations of every original reference row and deduplicates the resulting pairs. Count slices are encoded from explicit digit columns, rather than extracted from the whole code by quotient and remainder.
- It reverses short-rule words and tested positions, rather than reversing candidate windows.
- It reverses interval words together with their bound lists. Its interval test requires the entire represented count bucket to lie in the interval, treating symbol six as [6,21].
- It combines reference, short and interval masks once per direction, then applies the emitted-history masks independently for each compatible block.
- It derives the saved block boundaries directly from the source graph's direction/history arrays and compares each expected increasing code list with the entire corresponding saved slice.

All 37,875 possible blocks were examined. Every one of the 791 compatible blocks matches exactly; every one of the 37,084 incompatible blocks is empty. The factored comparison covers 23,561,280 direction/count pairs and 36,904,896 compatible candidate keys. It retains exactly 4,947,008 rows, with zero differing blocks, no missing codes and no extra codes. The three active history-guard placements are included. The independent block counts have raw little-endian 64-bit SHA-256 `a2f3272cdbccb776b6f3ef8f8dfa3e94a0f5c8fc3daa97facdf04897518c4d85`, which also matches the complete count list in `array-order-audit.json`.

The reference-placement counter in this checker counts each reference key at each matching direction/offset, giving 509,367 key instances; it is not a count of distinct direction/offset groups. The short-rule and interval counters give 7,927 and 4,279 oriented placements, respectively. These counters describe predicate evaluation and are unrelated to the number of stored graph edges.

This closes the computational accepted-set comparison requested here. It does not convert the saved NumPy arrays or their hashes into Lean data theorems. The remaining checked assembly must instantiate the same acceptance predicate with the already checked actual-window/retention theorems, preserve the two reference-refutation premises, and establish one-sided finite-table membership coverage in Lean or through a suitable checked certificate. Full equality is sufficient and stronger. The full-key rank construction then supplies exact stored edge indices. Parallel endpoint pairs, weight interpretation and the other global proof obligations retain the limitations stated above.

## Reproducible order audit and generic Lean enumeration review

The exact order, rank, endpoint, metadata-chain and endpoint-pair multiplicity checks are now saved in `scripts/check_order.py`, SHA-256 `8fe7c5f1910d52b6e12375b78c35dcdfaef2b73b968131cfc2cadad79bf11055`. Run this script with the project Python runtime from the repository or any working directory; it resolves all input paths from its own location and writes `data/array-order-audit.json`. It pins every source/data input, checks those pins again before success, and records its own hash. When a receipt already exists, it preserves those exact bytes under a hash-derived filename before replacement; an existing different backup is never overwritten.

The fresh run passed with exit code zero in 1.719 seconds. Every previously recorded substantive result agrees with the original receipt. The current receipt SHA-256 is `e3096ad1e30227d992ab5c4fd926a114208455a1eb71b1c353c1ea05bb8c4cdf`. The previous receipt remains byte-identical at `data/array-order-audit.previous-f5db16e24474e7ea.json`, SHA-256 `f5db16e24474e7eaceecc1742d8c7acf3edb5f72c0402b7bf8de6be1e5433d8a`. The independently checked retention-equality receipt is unchanged.

`lean/RetainedEnumeration.lean` was read in full at SHA-256 `de5dc56da9c55f864bcdf692be80ded05199f380b2acd9bda00135ed79cb828e`. No defect was found in its stated generic scope:

- `accepted_code_iff` and `generated_row_iff` characterize a generic Boolean predicate's finite enumeration over 505 direction IDs, 75 history IDs and 46656 count codes.
- `RetentionCover` states only that every bounded accepted key occurs in the supplied row list. `retention_cover_iff_subset` expresses precisely this one-sided inclusion. Extra saved rows are allowed.
- `exact_generator_covers` and `saved_row_index` use exact equality as an explicit sufficient premise. `covering_row_index` needs only `RetentionCover` and supplies an index whose optional lookup returns the key. Such a successful lookup entails an in-bounds list index; the theorem does not itself return a `Fin` value.
- `retention_cover_mono` correctly permits adding rows. Additional rows still require whatever endpoint, weight and potential checks the later graph argument uses.
- `prefix_rank_index` and `flattened_block_index` provide the prefix-length-plus-first-position formula under explicit block membership. They do not identify a concrete saved block by themselves.
- `full_key_index_unique` requires a `Nodup` hypothesis on full keys. It makes no endpoint-pair uniqueness assertion. `indexed_endpoint_maps` transports a found row index through arbitrary source and target maps without requiring unique endpoint pairs.

Accordingly, one-sided accepted-key coverage suffices for this membership step. The earlier wording in this report that required full equality has been weakened to the sufficient coverage requirement; the successful computational equality remains stronger evidence. The file is parameterized by `keep` and `rows`. It neither instantiates `keep` with the intended numeric retention executable nor proves coverage of the actual saved arrays. Its abstract endpoint maps also remain to be identified with the saved `U` and `V` columns.

The Python reconstruction in `scripts/check_arrays.py` compares numeric predicates with saved arrays. It is distinct from the forthcoming Lean `NumericRetention` implementation and provides no automatic correctness or equivalence theorem for that executable. Linking the actual-snake retention lemmas, the executable predicate and the row-coverage certificate remains an explicit assembly obligation. This was a read-only source review; no fresh Lean compilation was run or claimed by this reviewer.
