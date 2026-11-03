# Direct reference coverage candidates

The bounded scan found five new candidates among the 1378 reference keys. All five use the exact direction word $012032$. The scan inspected the ten entries with that direction word and compared their count intervals directly with the three selected local refutations. It did not apply reversal, relabel a different stored word, or transfer a longer window.

| Zero-based index | Count symbols | Proposed refutation |
|---:|---|---|
| 196 | $(2,2,6,5,2)$ | Second count at most two and fourth at most five |
| 197 | $(2,2,6,5,3)$ | Second count at most two and fourth at most five |
| 198 | $(2,3,6,3,2)$ | Second count at most three and fourth at most four |
| 199 | $(2,3,6,3,3)$ | Second count at most three and fourth at most four |
| 200 | $(2,3,6,3,4)$ | Second count at most three and fourth at most four |

Symbol six remains the interval $[6,21]$. Each candidate interval is contained in the corresponding proposed refutation bounds. In particular, the unrestricted middle count retains its full interval; no exact-six substitution is used. The second-count-at-most-one refutation contributes no direct catalogue match.

None of these five keys occurs in the fifteen entries already discharged by `ReferenceCoverage120`. That earlier successful receipt, its source, compiled object and log hashes were checked. The new combined list has twenty distinct members of the reference union, and an independent literal filter leaves 1358 entries.

`lean/ReferenceCoverage121.lean` is prepared with four statements:

- `twenty_reference_entries_refuted`, applying the existing centre-bound weakening lemma to the five candidates and then reusing the previous fifteen-entry theorem;
- `reference_union_iff_remaining_twenty`, retaining the remaining refutation obligation explicitly;
- `remaining_twenty_key_count`, with proposed kernel checking of the exact count 1358;
- `new_reference_indices`, with proposed kernel checking of all five index equalities.

There are no new definitions. The proof uses only direct interval containment for the raw local refutations. The actual-snake reversal result is not used to infer a reversed local `Refuted` proposition.

The new source has not been compiled. Both its concrete `ActualPair121` dependencies and this catalogue instantiation remain pending. Accordingly, these five keys remain candidates in this report; the review does not change the currently checked fifteen-entry status. A successful check would reduce the catalogue obligation to 1358 entries, without proving those remaining entries or establishing a global snake bound.

Exact output pins:

- `data/reference-coverage-candidates.json`: `f543f5c9a347d01c7797efa982e4f9f1201d22f491cf8bd448e32448307339a5`.
- `lean/ReferenceCoverage121.lean`: `3d60dbf4867f1fedae1016f605b8cefaa6907b84b075ee515b74ef132147ea8a`.

The JSON includes all 22 source-chunk hashes, prior receipt/object/log pins, exact candidate intervals, selected refutation names and the current uncompiled dependency-source hash. No compiler, solver, graph computation, Git action or existing-file edit was performed for this subtask. The reported snake-bank scan and boundary probes were outside its scope.
