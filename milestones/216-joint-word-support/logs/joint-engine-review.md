# Joint-engine source review

No blocking correctness defect was found in the new pair-projection code or its per-job isolation. This is a read-only source assessment. No compiler, software tests, solver or native continuation was run.

Coverage: the entire 459-line `joint_solver.c`, the entire 143-line `joint_continue.py`, their complete diffs against round215, and the three statements in `Joint216.lean` were read. The unchanged family and symmetry machinery remains dependent on its existing mathematical assumptions and input interpretation.

Reviewed SHA-256 pins:

- `216-joint-word-support/scripts/joint_solver.c`: `6d025faf3620933ceaab7fd12c5d180f1c1bd6142e67de53950012fb162b1e91`
- `215-word-partner-capacity/scripts/word_solver.c`: `b9dc79b25ff57219066babfe3f10355823ad10605aa199318826e0cbf558df1e`
- `216-joint-word-support/scripts/joint_continue.py`: `0f464816a4f862a6482966cab8f70f12e7b2b4afdabcd882d9f0bc0aeadacb36`
- `215-word-partner-capacity/scripts/word_continue.py`: `44cf914f35468428fea3b9cd938182a23a7743bb247acd91ae81ca7bf0f14276`

## Projection and relation orientation

At C lines240–260, the three temporary tables are exactly the three pair projections of assignments satisfying all three current relations inside the current root domains. The complete support tables for one triple are computed before any of its three relations is modified. Later triples may use earlier restrictions; this is sound by successive preservation of every fitting complete assignment.

At lines216–234, deletion is restricted to pairs inside the current root domains and already allowed by the relation. Both orientations are changed as transposes. Input transposes are constructed at lines399–405, and the new code preserves this invariant. A missing relation is interpreted as universal and is materialized in both directions only when an actual deletion occurs. Initializing a new relation leaves every pair outside the deleted root-domain pairs allowed. Degree counts are increased once per new relation. The next propagation call queues every current relation, including new ones.

The alphabet-size branch avoids shifting by64. Temporary arrays have64 rows, while admitted domains are restricted to the configured alphabet. Triple indices are distinct and remain within the variable count.

## Root restriction, descendants and continuation

At lines352–363, the node counter is incremented before propagation. Only its first value triggers projection, after the initial ordinary propagation. The counter is never reset in the recursive traversal. The maximum is four projection sweeps, each successful restriction sweep followed by ordinary propagation. A sweep with no table change needs no further propagation. Stopping after four sweeps may leave further deductions undiscovered; it does not invalidate existing deductions.

Every descendant copies a parent domain vector and restricts one entry; subsequent propagation only removes values. Consequently every descendant, including sibling descendants, remains inside every root-domain vector used for projection. Tables are never strengthened from a descendant's narrower domains. This is the relevant containment condition for `Joint216.projection_preserves_subdomain_assignment`.

The driver starts a fresh process for every submitted job at Python line59 and supplies the original pinned input tail at lines48 and62. No learned relation table is serialized into a later job. Pending vectors are checked to be subdomains of the submitted vector at lines91–93. Reloading the original tables can discard useful inferred restrictions, but it does not omit a previously possible completion; the next job can derive restrictions again. A resource interruption before a valid result leaves the submitted state unchanged.

## Proof boundary

The new native operation is a consistency operation for arbitrary binary input relations. It does not assume that variable indices represent consecutive snake groups, and it does not hard-code Hamming distance zero or two. Selecting consecutive indices merely selects which triples receive this sound consistency operation. Therefore its solution-preservation argument does not require a new geometric assertion about every input table entry.

`Joint216` states preservation for three arbitrary Boolean relations, given membership of the actual assigned values in the domains and satisfaction of the original relations. Those hypotheses match the mathematical reason for the new operation. This review does not identify the C bitmask computation with the Lean list computation through a checked executable bridge.

For a snake conclusion, the separate obligation remains that every intended path completion satisfies the supplied binary tables, family inequalities, partner assumptions, symmetry restrictions and other input constraints. The generic projection result does not establish those premises or certify complete native traversal. Likewise, the distance-two geometric result alone is not an identification of all serialized model rows with the intended path conditions. Existing concrete path and model evidence must retain its own scope.

No native speed improvement, new exclusion, or global bound follows from this source review. The saved-domain analysis shows extra pair restrictions and no immediate unary gain; runtime usefulness remains to be measured separately.
