# Round 212: spare capacity and partner support

The hypothesis was that the unused parity-word allowance can turn the round-211 aggregate count into a sound domain restriction. The deduction is proved, its generic assignment-level composition passes Lean, and a native implementation is active in the retained-coordinate case [0,6]. The case remains open. No new Q9 construction, global bound or completed six-coordinate exclusion is obtained; 196 remains unresolved.

## Argument

Within one parity alphabet of q words, let C be the chosen interval family and O the outside family. Each family requires distinct assigned words. For each outside interval x, its listed partners contain every member of C with which it can share a word. Let P_x be the union of those partners' current domains, and let s=q-|C|.

At most s outside intervals can use words absent from C: the chosen values use |C| words, and outside values are distinct. If D_x and P_x are disjoint, x is necessarily one of these unshared intervals. More than s such forced intervals contradict capacity. If exactly s are forced, every other outside interval must share with a listed partner, so restricting its domain to P_x preserves the same complete assignment. The forced intervals keep their unshared options. Before capacity is reached, this reasoning permits no individual support restriction on another outside interval.

For the saved source and retained pair [0,6], the even family has 30 chosen and 9 outside intervals, with spare allowance 2; the odd family has 26 chosen and 13 outside intervals, with allowance 6. Each family therefore needs at least seven shared words. These are separate parity alphabets.

There is also a group restriction. For J contained in O, let N(J) be the chosen intervals that are listed partners of some member of J and have a current domain intersecting that member's domain. Every shared member of J determines a distinct partner in N(J); at most s members remain unshared. Therefore

\[
|J|\le |N(J)|+s.
\]

The zero-support rejection is its special case N(J) empty. The general group rule can detect competition for a small partner set even when every interval has individual support. It is proved as a generic deduction, but has not been integrated into this round's search engine. Exhaustive examination of all outside subsets in the eleven saved regions finds no violation: the largest partner deficiency is 1 in each parity, below the respective allowances 2 and 6. Thus there is no immediate additional exclusion at this cutoff. This observation makes no claim about deeper search states or speed improvement.

## Checked logic and remaining premises

A supplementary written argument in logs/orientation-note.md shows that the full group condition is independent of which corner is chosen from each opposite pair. If k intervals of one parity use r repeated opposite-corner pairs, they use k-r distinct words, requiring r>=k-32. The candidate equality graph must therefore have a matching of size at least k-32. This is equivalent to the complete collection of partner-subset inequalities. A matching alone need not admit consistent word labels; the note includes a counterexample. This equivalence is written and reviewed by the coordinator, without a new Lean or implementation claim.

Three new Lean modules pass with eight reports. SpareSupport212 checks rejection, saturation, supported values and preservation under domain filtering. SupportBridge212 derives the exception-index budget from assigned words, derives missing-support implies exception, and composes the domain rule without assuming its actual exception list. PartnerSubset212 proves the group inequality. Accepted dependencies contain only propext and Quot.sound, with no admitted proof in the accepted results. The first bridge attempt stopped for low free memory; a later attempt exposed a list-membership simplification error, which was repaired. Failed logs and successful source/object receipts are retained separately.

These results retain distinctness, partner completeness, domain fitting and alphabet hypotheses. The square geometry gives a written justification; the complete arbitrary-snake-to-model Lean assembly, literal native masks and complete native traversal certificate remain unfinished. An independently reviewed native implementation is a separate evidence level from these generic Lean deductions.

## Native model and saved search

The fresh complete root uses the unchanged original case-22 model: 78 domains, 2,600 binary relations, 120 excluded source-isometric assignments and 120 residual permutations. The previous nonresumable two-second run contributes no inherited coverage. The input audit verifies the complete original input prefix, both appended support families, all 41,312 required equality exclusions and all original root domains.

The search accepted 120 transitions: 104 exhausted subtrees and 16 limited runs. It examined 1,051,511 nodes in 76.077 reported solver seconds, recording 63,089 support-value removals and 311 support contradictions. These are repeated operations across branches, not distinct globally excluded assignments. All jobs exited normally; the batch ended at its stated budget. Its final eleven regions are preserved. The complete saved chain reconstructs byte for byte under independent review, while full traversal certification remains pending.

The [0,5] state remains frozen in round211, and [0,4] and [3,4] in round209. Only [1,4] is exhausted among the 28 six-coordinate choices, leaving 27 unresolved. The source-specific six-changed-history requirement from earlier four/five-coordinate enumerations is unchanged.

## Publication and handoff

Both existing editor documents are updated and compile successfully, with exact paper mirrors, all three authors and the local main-paper hyperlink settings preserved. The contributor branch remains at c999e9bd, reporting 3125/3127 certificates; no new merge or independent rebuild is claimed. The completed archived 235 theorem retains its saved successful audit, with independent full rebuild pending. The routes to 234 and 233 remain conditional; the verified construction remains 191 edges.

The user requested a pause after this round. Finish the exact scoped publication and pause the goal; resume research only after a new instruction. On resume, the saved case can be continued with its pinned engine. The group inequality should be evaluated as a possible stronger rule without assuming it improves performance. A direct completion of the geometric-to-model proof would reduce a known verification gap. No software tests were created or run.
