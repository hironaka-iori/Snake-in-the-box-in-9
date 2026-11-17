# Round 234 final document review

Review scope: all round-234 changes against the saved before snapshots; the complete new main subsection sec:exchange234; its preceding round-231/232 construction premises; the full current main abstract; both date and bibliography changes; the new short explanation section; and all of MATHEMATICAL_NOTE.md. No manuscripts were edited. No compiler, solver, or tests were run.

## Findings

No blocking mathematical error was found in the new overlap deduction, isometry transport, or restricted maximum, under the stated finite-cover premises.

Two minor wording improvements are recommended:

1. Main manuscript, lines 8695–8699, beginning “There is also an exact restricted maximum.” The conclusion is correct for the union of all permitted classes, with attainment in its zero-replacement part. To prevent an interpretation that every individual exchanged class attains 191, use: “Over the family of paths for which one complete parity class has 96 vertices and differs from a saved class by at most one replacement, the maximum length is 191.” The existing following explanation establishes the bound and the attaining seed. The analogous MATHEMATICAL_NOTE.md paragraph at line 37 already mentions the zero-replacement part of the family, but may use the same explicit family wording.

2. MATHEMATICAL_NOTE.md, line 19, says “Its final receipt is required for the complete-cover claim.” The requirement is satisfied: the saved independent static audit is PASS. Replacing that sentence by a statement that the audit completed would remove an obsolete impression of pending static verification. This does not affect the separate pending model/union audit described below.

The four elementary contradiction types are stated correctly. The saved certificates actually use three of them: 430 proper forced cycles, 302 available-degree contradictions, and 512 forced-degree contradictions. No articulation-type row is present in this certificate set. Describing the fourth rule as an available valid implication is sound.

## Mathematical checks

The exact exchange update and locality statements agree with the accepted ColourExchange234 source. Degree zero and degree three labels can newly become usable; labels incident to both exchanged vertices retain their degree but change their neighbour identities. The paper correctly separates the four checked relational statements from written cardinality consequences and finite code.

For a 192-edge candidate, its minority and majority classes have sizes 96 and 97. Relative to either saved 96-vertex seed class, minority intersection 96 is the round-232 fixed-class case, and intersection 95 is exactly one removal plus one outside same-parity insertion. The completed round-234 family excludes the latter, so minority intersection is at most 94. The round-231 majority cover excludes containing an entire saved 96-class plus one new vertex; therefore majority intersection with the other seed class is at most 95. The two disjoint intersections sum to at most 189.

The seed has 192 vertices and the candidate has 193. The omissions and additions are therefore at least 192−189=3 and 193−189=4. The claim concerns a complete candidate vertex set and does not assert that those minimum changes suffice.

Both parity classes of every one of the 131 saved seeds are represented: the current base provenance has all 262 seed/parity pairs, grouped into 145 distinct labelled sets. Applying the inverse cube automorphism to a candidate compared with an isometric seed copy preserves vertex intersections, inducedness, and length. Cube automorphisms preserve the bipartition up to exchange, and both classes are covered. The isometry extension therefore does not require an enumeration of isometric seed copies.

For the restricted maximum, a complete selected colour class of size 96 gives at most 192 edges by alternation. At length 192 it necessarily is the minority class, so the fixed-class or one-replacement exclusion applies. This leaves at most 191. An original seed lies in the zero-replacement part and attains 191. This is a restricted-family maximum, not a global bound and not an attainment statement for each exchanged 96-set individually.

The augmented Hamiltonian-cycle argument is valid for these 96-vertex classes. Removing the dummy from a spanning cycle gives a Hamiltonian path between two distinct supported vertices, and adding it reverses that operation. The forced-edge and vertex-deletion arguments are stated with the correct necessary-cycle interpretation.

## Evidence read

- The independent static audit has status PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT and covers 2,227,200 descriptions in 13,920 cores. Its counts match all six outcomes stated in the main subsection and mathematical note, including 1,381 surviving descriptions and 1,325 distinct classes.
- The elementary replay has status PASS_COMPLETE_REPLAY, checks all 1,325 rows, and certifies 1,244 contradictions. Its remaining 81 rows are explicitly unresolved by that replay; the paper correctly assigns them native circuit evidence.
- The first native result is TIME_LIMIT with 771 completed INFEASIBLE rows. The resumed result is COMPLETE_QUERY_BATCH with 22 INFEASIBLE rows. Direct set comparison of the recorded class IDs gives 59 native-only classes from the first batch and 22 from the second, with 81 native-only classes in total and no uncovered candidate ID.
- The resumed source bytes match its recorded source hash. Its 22 base records equal the corresponding original candidate records, preserving class IDs and selected vertices.
- ColourExchange234 has PASS with four axiom reports. Its current source, object, and compiler-log hashes match the receipt. No additional Lean claim is inferred from the native results.

At the initial review, the separate model/union auditor was still completing; its final receipt was not yet present. That pending status is resolved by the accepted final-cover receipt recorded in the addendum below. The class-ID union above remains a read-only consistency check of the saved results, not this reviewer's independent reconstruction of the 793 native models. No native solver result was rerun here.

Evidence hashes:

| Record | SHA-256 |
| --- | --- |
| data/exchange-audit.json | 0eef4aaf9ec6441a32904eb21270ffa3a906eee97b7cad092a0c7eb526d24be4 |
| data/forced-replay.json | 1c271e2d4e082667542b8666a9c164c11e718412c71161dbd0424f2bf434dd91 |
| data/hamilton.json | 1bf077a1e893b5dcd09b2a29e2f14da840ffbec8eeed7d9832321eb0f00c659e |
| data/hamilton-resume.json | 8e7fca32a0baee2416d29e49320155980d9d7885b040d5de23bdbc81bcccfa01 |
| data/ColourExchange234-audit.json | a7422c067898c9cc092844ee787a5755a5b13da96901bbe64e3eb36993359ee6 |

## Original-file preservation

Both editor originals match their E:/Snake-in-a-box/paper mirrors byte for byte. Each entire preamble is unchanged from its before snapshot after excluding the intended date command. The three author names and their order are unchanged. The main hypersetup block is identical; the short document has no explicit hypersetup block and retains its original hyperref hidelinks option.

Every pre-existing label is preserved. The main adds sec:exchange234 and prop:overlap234; the short document adds no labels. The research234 bibliography entry has the three authors in the same order, the round-234 title and date, and the intended milestone path. The main abstract retains the independent-rebuild qualification on the global 233 bound and states the new overlap result under finite/native evidence.

| Reviewed artifact | SHA-256 at initial review |
| --- | --- |
| D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex | 528163465d618eb322a744d0bbeaa30e8823671762800ccdc8487f0fb693b89a |
| D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex | 85ad5a6da3086202834fdfd3b07dd4b5e297a154113c351d76a8515682c7c613 |
| E:/Snake-in-a-box/milestones/234-single-colour-exchange/MATHEMATICAL_NOTE.md | 51b11608f809bc4d6b5b63fe2db601936a2ebc6babb523bef12b84da1b98cc93 |

The main before snapshot has hash b7d4060eff1a496ae20f914cb073e628e92a5cdf26d71b6e3f8c73597af2eec7; the short before snapshot has hash 9180c81346644701946fff1b7bfc3c7afa11fdef0dc61e076b885b0cc2ed6d59. This is a source and evidence-scope review. It does not establish successful compilation, visual layout, Git publication, or independent rebuilding of earlier contributor results.

## Final-version addendum

Both recommended wording refinements are present. Main line 8698 now states “The maximum over this family is 191,” followed by attainment in the zero-replacement case. MATHEMATICAL_NOTE.md line 19 now states that all 2,227,200 static decisions were accepted and that the final coverage audit accepted all 1,325 graphs, all 793 exported native models, and their exclusion union. No mathematical issue remains from either initial wording finding.

The saved final-cover receipt has status PASS_COMPLETE_CANDIDATE_UNION_COVER and SHA-256 d2a27ca944d8e544d2cda3b8d3a4fdeb67bef46c3efe3dc9b3ff984bc7be6cd2. It confirms 1,244 elementary-certified classes, 81 essential native classes, 793 verified native models, and an empty unresolved-class list. Its execution summary retains the initial native batch's partial-result history and the separate completed 22-row batch.

This resolves the previously pending model/union audit. Its stated limits remain: no solver rerun or native contradiction-certificate replay, no repeated elementary step replay beyond checking that replay's receipt and pins, and no end-to-end Lean graph extraction. The final manuscript preserves these distinctions.

The main and short originals still match their repository mirrors exactly. Both complete preambles, excluding the intended dates, still match the before snapshots; author order and PDF settings remain preserved. The short source is unchanged from the initial review.

| Final artifact | SHA-256 |
| --- | --- |
| D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex | df1fbd4ed8fc40a65410e317cb3409bd75ccaa5e5570d4598f12bef36d66f54d |
| D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex | 85ad5a6da3086202834fdfd3b07dd4b5e297a154113c351d76a8515682c7c613 |
| E:/Snake-in-a-box/milestones/234-single-colour-exchange/MATHEMATICAL_NOTE.md | 613349a0e12e5a2a58a7df7f97f137bdff5b4c58a63f03e804768f802788cacd |

This addendum reread the changed passages and final audit receipt only. It did not run a compiler, solver, or tests, and it does not report the outcome of the parent's ongoing manuscript recompilation.
