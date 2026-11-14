# Final support-argument source review

Date: 2026-11-14. Read the complete `SupportBridge212.lean` and `PartnerSubset212.lean` sources. No mathematical soundness concern was found under their stated hypotheses. This is source and argument review, without a compiler run or new claim about successful compilation.

`SupportBridge212.exception_budget` correctly applies the previous spare-capacity inequality to the lists of assigned words. Distinct assigned values in both the clique and outside lists are explicit. Mapping the filtered outside identifiers to their values preserves the relevant length, so the count of outside identifiers whose values are absent from the clique is at most `pool.length - C.length`. The earlier inequality also supplies the required relation between clique and pool lengths; natural subtraction is therefore safe.

`unsupported_exception` correctly uses the assumption that every actual clique sharer is a listed partner, assignment fitting within partner domains, and inclusion of those domains in the support list. If an outside assigned word were in the clique, it would belong to support, contradicting the missing-support premise.

`saturated_support_preserves_assignment` constructs the actual exception list, derives its capacity bound, places all distinct forced identifiers inside it, and applies the previously proved support-filter implication. The selected variable is explicitly outside and absent from the forced list. No claim that every outside variable must share is inserted. A list of exactly enough forced exceptions is sufficient; counting additional forced exceptions is unnecessary for this preservation implication.

`PartnerSubset212.partner_subset_capacity` has the correct bound

\[
|J|\le |N|+(|\mathrm{pool}|-|C|).
\]

Here list lengths are intended. Every assigned value from \(J\) either occurs in the clique or is an actual exception. In the first case, partner completeness and current-domain fitting give a partner whose domain intersects the chosen outside domain, and the stated hypothesis includes that partner in \(N\). In the second case, its identifier lies in the already bounded exception list. The distinct assigned values in \(J\) therefore inject into the union of these two lists of values, giving the displayed length bound.

The explicit `(J.map values).Nodup` premise matters: merely requiring every entry of a list \(J\) to belong to the outside list would allow repetitions. No distinctness or subset condition on \(N\) is needed for soundness; extra entries or repetitions only enlarge the bound. Likewise the pool may be a list with repetitions, which weakens its capacity bound. For the intended model it is the actual 32-word parity alphabet.

These sources supply conditional finite-list deductions. Instantiating their assignment-fitting and partner-completeness premises requires the concrete model inequalities and domain interpretation. They do not certify the C execution, the native traversal, or the full geometric reduction. The partner-subset inequality is not implemented by the reviewed round-212 support engine; that engine uses only the forced-unshared count and saturated support filter.

SHA-256 pins:

- `lean/SupportBridge212.lean`: `c1f687a0a40499881115d7c48ce1dc638c8980363e36b919b4c1a8cff8810b2f`.
- `lean/PartnerSubset212.lean`: `6aba653343e45446833dc1b15968f9dd5b498e8567d2448d88e05dae277c18ce`.

Paths are relative to `E:/Snake-in-a-box/milestones/212-spare-support/`. No mathematical or executable source was modified.
