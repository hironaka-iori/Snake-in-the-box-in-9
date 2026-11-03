# Source review of three additional reference instantiations

`lean/ReferenceCoverage120.lean` is prepared and has not been compiled in this task. It imports `ActualOuter120` and `ReferenceCoverage109`, introduces no definitions, and requests four axiom reports. No reference is newly marked discharged by this source review.

The three candidate entries have the same direction word $012031$ and symbols

$$[2,3,6,3,2],\qquad[2,3,6,3,3],\qquad[3,3,6,3,2].$$

Their zero-based positions in the exact1378-key union are126,127 and138. The symbol6 denotes $[6,21]$. Each candidate's four outer intervals lie inside $[0,3]$, and its middle interval lies inside $[0,21]$. Therefore the existing `refuted_of_tighter_centres` lemma can transfer `ActualOuter120.outer_refuted` to each exact candidate, once the dependency theorem is successfully checked. The direction word and centre geometry are unchanged.

The source uses three successive applications of that lemma, with `Tags.centresK_eq` before the finite checks. This matches the checked milestone108/109 approach and avoids the earlier centre-computation reduction issue. After the three new entries, the remaining proof is exactly `Snake9.RelaxedGraph109.twelve_reference_entries_refuted`; it does not reconstruct or assume those earlier refutations.

The exposed APIs in `Snake9.ReferenceCoverage120` are:

- `fifteen_reference_entries_refuted`, for a literal list consisting of the three new candidates followed by the previous twelve entries.
- `reference_union_iff_remaining_fifteen`, obtained from the existing `allRefutedList_filter_iff` lemma.
- `remaining_fifteen_key_count`, asserting that the exact union filtered by this fifteen-entry list has length1363.
- `new_reference_indices`, giving the exact `referenceKeys.getD` equalities at126,127 and138.

An independent Python literal check confirms that the list has fifteen entries, all occur in the union, the three new indices are correct, and filtering the1378 literals leaves1363. These checks support source preparation; the Lean count and index statements remain pending. No claim is made that the remaining1363 references are refuted, or that the new global graph obligations are closed.

Source SHA256: `c03842cad88cf8e55c6b22f5c86914233c43d4b19c4fa77c1ec4fef2b2f1414c`.

The candidate scan is preserved separately in `data/reference-coverage-candidates.json`, SHA256 `4a1639cdd32891b51c6e81dedc17d9ccd36283a1ae03443acb2c9d465e8d90a3`. Its status remains `UNCHECKED_COVERAGE_CANDIDATES_ONLY` until a successful instantiation receipt is available. Only the new source and this review were written; no compiler, solver or Git command was run.
