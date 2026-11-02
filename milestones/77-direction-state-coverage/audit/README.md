# Direction and state table audit

The ordered direction tables and history compatibility data passed an independent small Python audit. No table mismatch was found. This establishes finite-data consistency; it does not establish the arbitrary-snake graph interpretation or any new upper bound.

## Authoritative data and ordering

- [Milestone59 metadata](../../59-extended-share-window/extended/data/model.json) is the source consumed by the current builder. Its `direction_shapes` list contains 132 canonical eight-transition words. Its `extensions` list contains 505 canonical nine-transition words. All IDs are zero-based list positions.
- [Milestone59 construction](../../59-extended-share-window/scripts/extend.py), lines 13–14 and 50, inherits the eight-word list from milestone58 and obtains the nine-word list from `model.words(9)` in [milestone42](../../42-six-count-state-model/scripts/model.py), lines 17–21. That generator traverses first-occurrence canonical words by increasing next symbol, rejecting every prefix that repeats a vertex or introduces a chord. Its output is lexicographic. The inherited eight-word list is identical to milestone42's eight-word `extensions` list as an ordered list.
- [Milestone70 builder](../../70-proof-supported-share-model/scripts/build.py), lines 33–35, assigns `di` by enumerating the exact nine-word list. It assigns the source index from the canonical first eight entries and the target index from the canonical last eight entries. The geometry lookup at line 54 uses the same nine-word ID. The saved geometry rows agree in exact order.
- The lists retain both orientations. The 132 eight-word entries have 77 reversal classes, and the 505 nine-word entries have 270 reversal classes. Reversal minimization must not be used when defining these graph IDs.

The independent check enumerated all 4,140 restricted-growth words of length eight and all 21,147 of length nine. It used contiguous-block parity, separately from the builder's vertex-pair algorithm. The 132 and 505 survivors match both saved lists in exact order. All entries are distinct and use coordinates below nine. Both source and target maps reach all 132 shapes.

The extracted lists and source/target maps are retained in [ordered-tables.json](ordered-tables.json). Its SHA256 is `ca96ecafa0045d46db8c09dff1b8c504bba618de17e146547479af13b26c2611`.

## History compatibility

[Milestone67 construction](../../67-critical-family-charge/scripts/build_full.py), lines 30–32, defines the dictionary as the empty word followed by all one- and two-ID proper prefixes of its retained three-ID signatures, sorted by length and then lexicographically. There are 75 distinct entries: empty, 31 of length one, and 43 of length two. Milestone70's ordinary and enriched metadata retain exactly the same dictionary, compatible-shape list and pattern list.

For each nonempty history index q, the compatible shape is exactly the target-shape index of the final nine-word ID in its stored prefix. Index zero has no prescribed shape; the state retains the eight-word shape separately. Every two-ID dictionary prefix satisfies target(first ID) = source(second ID).

The independent check examined all 75 × 505 = 37,875 dictionary-update pairs. The maximum-length matching suffix is unique in every case. There are 2,363 nonempty updates across this full Cartesian product. Every such update ends in the newly supplied ID and has compatible shape equal to that ID's target shape, even before applying the source-compatibility filter. Exactly 791 pairs satisfy the builder's source-shape filter, including all 505 pairs at empty history. These numbers describe small direction/history combinations, not full graph edges or reachable states.

The 75 prefixes and 58 signatures match the literal lists in the checked milestone75 source. The previous milestone74 audit hashes milestone70 enriched-model.json; its hash agrees with the current bytes. Milestone67 full-model.json has a different whole-file hash because it is a different file. The relevant history tables agree across these sources. An initial cross-file comparison incorrectly suggested metadata drift; inspection of milestone74 source_audit.py resolved that issue.

For an actual window sequence, the shortest compatibility argument is symbolic. A nonempty stored suffix ends in the previously read ID. Its compatible shape is therefore that previous window's target shape. The adjacent-window shift identity equates this with the new window's source shape. After reading the new ID, any nonempty stored suffix ends in that ID and consequently has its target shape. This argument requires the numeric history index to denote the stored longest suffix and requires initialization at index zero. The existing history theorem alone does not identify the numeric index with the builder's list position.

## Exact interfaces and coverage risks

1. Prove membership and uniqueness for the canonical eight- and nine-transition words before using an index lookup. A default value from a failed lookup must not silently represent a real shape. The existing `snake_inducedPattern_block`, `canon_isRGS`, `length_canon`, and `inducedPattern_canon` reduce actual windows to finite canonical coverage. The six-word coverage proof offers the same method, with separate eight- and nine-word tables.
2. Preserve the exact oriented ordering. A complete set-membership theorem does not establish that a numeric ID agrees with the current arrays. The finite tables need distinctness and lookup equalities, together with their recorded ordered bytes.
3. Reuse [milestone74's shift identities](../../74-graph-interpretation-audit/lean/WindowStateShift.lean): `canonical_nine_source` and `canonical_nine_target` already identify the two actual eight-word blocks. What remains here is their connection to the exact finite indices. The share-suffix identity concerns six words and a different lookup.
4. With a snake of m edges, there are m−8 nine-transition edges for m≥9, starting at r=0 through m−9. There are m−7 associated eight-word states, starting at r=0 through m−8. The terminal state requires eight-word coverage even though no nine-word edge starts there. The target offset is r+1.
5. Nonempty history blocks suppress the explicit shape index only because the compatible-shape invariant holds. The update dictionary contains valid suffixes, but arbitrary history initialization is not justified. Index zero must start the actual run.
6. Shape compatibility does not identify all eleven-transition coordinate realizations of three IDs. Forgotten coordinates can return, and one signature can have multiple realizations. This later share/exclusion coverage obligation remains independent of the present nine-word coverage.
7. Direction IDs, eight-word shape IDs, dictionary IDs and global graph-edge IDs are different index types. Milestone67 builds edges with history as the outer loop; milestone70 builds with direction as the outer loop, then history, then increasing count code. Thus older graph edge positions cannot be reused as current edge positions. Milestone72 filters preserve the retained milestone70 order, while its share update only changes weights.
8. The metadata of the current source graph and mixed comparison agree on endpoints, direction IDs, count codes and history-array hashes. Their common size is 1,601,856 states and 4,947,008 edges. This audit did not reload those large graph arrays, prove every exclusion guard, or verify any potential.

## Reproduction and limits

Run [audit_tables.py](audit_tables.py) with Python. It imports no model module and executes no solver or Lean process. It independently checks parity coverage, exact ordering, source/target maps, inherited table consistency and the small history updates. [table-audit.json](table-audit.json) records the result, semantic table hashes and SHA256 hashes of 23 inspected source/data dependencies.

The source inspection covered the relevant generation, filtering, normalization and history code. The inherited proof sources were read for interface statements; their prior receipts were pinned without rebuilding them. No Git mutation, live certificate edit or file write outside this audit folder occurred.
