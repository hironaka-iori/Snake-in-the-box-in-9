# Independent post-edit paper review

Current reviewed source: `paper/snake9_research.tex`, 3,999 lines, SHA-256 `eb9d5581336060b799e93b7532f59cdb485ce7f5ee39b28bd2f0fdfba4a09ec3`. Current counts: 130 statement blocks, 190 labels and 14 new Lean theorem audits across two modules.

The original review below examined the 3,935-line version `8e9ee179a080ff5049ff6731bac6d5676b0c670762e4a07270852492258857ef`. Its line references and seven-check receipt describe that version; the bounded bonus-criterion addendum below records the only subsequent changes.
Baseline: `milestones/86-paper-revision/data/paper-before.tex.snapshot`, SHA-256 `3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd`.

## Verdict

No unresolved mathematical or status correction was found in the revised material after the two corrections below. This is a bounded source and evidence review. It does not certify the remaining global graph-to-snake assembly or the historical upper-bound dependency closure.

The complete original paper was read for `pre-edit-review.md`. This review read the complete revision diff, including every added statement and proof, and rechecked the final changed passages. The first reviewed revision has 128 statement blocks: all 123 previous labels remain, only `thm:countfree-completed` has a strengthened previous statement, and five propositions are added. The unchanged statement bodies number 122. These counts include definitions and conjectures. The preamble, author order and hyperlink settings are unchanged; the repository and existing editor source have identical bytes.

## Corrections resolved

1. Line 1293 previously retained the stale assertion that the converse of signature recognition had no separate Lean check. It now reports the checked exact equivalence and numeric-history interpretation, consistent with milestone 77.
2. Lines 1311–1317 now explicitly replace dictionary identifiers by their unique canonical words in the ordered 505-entry table. This resolves the earlier mixture of word-valued symbols and numeric dictionary identifiers. Suffixes and lengths are preserved by this bijection.

Both corrections were reported during review and remain present in the current source.

## Mathematical scope of the additions

| Location | Reviewed conclusion and limits |
| --- | --- |
| Lines 1325–1359, `prop:actual-state-sequence` | For an actual snake with at least nine transitions, the stated state and candidate-step counts, count-code quotient/remainder, entering count and history compatibility agree with milestones 77–78. The final state is included. No retained-array membership is claimed. |
| Lines 1361–1395, `prop:local-filter-retention` | The four-count interval offsets start at direction offset two and count offset three; all three placements and both orientations are covered. The ten intervals use upper endpoints below six or 21, so truncation transport is valid. The 37 cap rules have caps below six; all three sum rules retain explicit unsaturated-symbol guards. Reversal maps internal position j to L-j. These agree with milestones 79 and 81. |
| Lines 1405–1437, `prop:history-exclusion-retention` | The three emitted signatures force the exact eleven-direction words using the exhaustive 81-continuation checks. Their required count positions are s+10, s+8 and s+10, hence sixth, fourth and sixth edge-count symbols when s=r-2. The lower bound three survives truncation and contradicts the tested upper bound two. No general uniqueness assertion for other history signatures is introduced. |
| Lines 1447–1477, `prop:reference-union-retention` | Both catalogue-refutation premises are explicit. The count-code extraction, widths two through six, allowed offsets, joint reversal and symbol-six interval [6,21] agree with milestone 85. The text distinguishes source-table cardinality checks from checked membership/retention and does not claim that the two closed catalogue dependencies have been imported. |
| Lines 1592–1644, `prop:unsaturated-cycle` and sensitivity discussion | On the same graph, nonnegative bonuses cannot reduce any cycle mean, while bonuses vanishing on edges with all six symbols below six leave the four-edge attaining cycle unchanged. Thus the mean stays 483. Summing a potential on this cycle gives p ≤ 483d and a strict-criterion deficit 2319d before any positive range. Changing the graph, restricting realizable walks or changing the boundary budget is outside the proposition. No actual snake realization is asserted. The conditional increase to 497 concerns this one cycle only. |

The strengthened count-independent theorem at lines 1032–1038 adds exactly the completed 012310 floor 12. Its arbitrary matching snake and reversal scope is supported by milestone 80. Five shapes have some completed count-independent bound, four meet their stated target floors, and five targets remain pending: 012032, 012034, 012301, 012340 and the stronger 012345 floor 16. The weaker 012345 floor 12 remains distinguished. The combined local receipt currently contains cases 7300, 7304, 7305 and 7306; it lists 7301, 7302, 7303, 7307 and 7308 as remaining. No final case7302 proof-audit receipt was present at inspection.

## Arithmetic and supporting evidence

Independent exact rational arithmetic reproduced all four displayed rows:

| Mean | Unscaled potential range | Derived fraction | Integer comparison |
| --- | --- | --- | --- |
| 480 | 536 | 10609/45 | 235 |
| 483 | 551 | 157625/669 | 235 |
| 9259/19 | 11301/19 | 20965613/89059 | 235 |
| 496 | 600 | 137941/587 | 234 |

The scale-19 convention is explicit. The zero-range single-target deficit is 25447. The unsaturated cycle totals 1932, with mean 483; the two proposed local targets add 56 to this witness and give 1988/4=497. The paper correctly keeps the latter calculation separate from a minimum-mean claim for the modified graph. The 480 comparison is historical; the completed-local model is 483 with range 551. The six historical weakening experiments remain six, despite the current five pending targets.

The seven new Lean audit entries were inspected in `data/logic-audit.json` (SHA-256 `1cc66e2ed3f509d954afadc363b8610f57033a6f4c5735267fb9713f67b9c01d`). The saved source, object and log match the recorded hashes:

- `lean/RevisionLogic.lean`: `91210ba078eaaffd5dfeebe16ab69c864244cd957c68aa44a71dca177f20c6c5`.
- `build/RevisionLogic.olean`: `9ffdef66eb0fe3288c18d440547a74c0d42f32deb9d7d2194ac7630f3982d6ae`.
- `logs/RevisionLogic.log`: `1a10022592c2c9019b05d4c4c334d0296968f65cffd2d0de14df0d9c516a1560`.

The log reports seven successful standard-axiom audits. Their scope is abstract cycle-family preservation, finite bonus sums and conditional arithmetic, with no graph membership or geometry assumption silently discharged. The three unused-hypothesis warnings are harmless. Milestones 77–85 summary/checkpoint receipts were reread and their statuses/hashes agree with the pre-edit audit; milestone 83 remains partial. Current `data/verification.json` (SHA-256 `499dc72fd609b353bce83b2ddad62e3cb56ac83b3442a9d81a16e65c45912790`) records the final paper hash.

All 187 labels and bibliography citations resolve without duplicate labels. The four newly cited pinned commits and their milestone README blobs exist locally. This is source/pin verification, with no external literature refresh. The maintained interval remains the archived contributor interval 191 through 235; the current work neither establishes unconditional 234 nor constructs or proves optimality of 196.

## Verification limits

No compiler, solver or large proof replay was launched for this review. Historical closed refutations and graph/interface results were evaluated through existing source and receipts, rather than rebuilding their full dependencies. Exact retained-array membership, all-compatible-realization credit coverage, complete potential replay and current import of the two reference catalogue closures remain outstanding. These are stated in the revised paper.

`data/editor-compile.json` records a helper failure before source compilation on the immediately preceding paper hash `c600cdff6034dce0d57b0d6b79d4a666556c4fc6eb234f1722be2ba2151f61b0`. It provides no successful compilation or layout check for either version. The final corrected source remains without a newly verified PDF. This is accurately disclosed in the milestone README and should remain explicit in delivery.

## Addendum: exact bonus criterion

The complete diff against `data/paper-before-bonus.tex.snapshot` was read. That snapshot has SHA-256 `8e9ee179a080ff5049ff6731bac6d5676b0c670762e4a07270852492258857ef`. The additions are precisely `def:zero-bonus`, `prop:bonus-criterion`, their explanation and proof, and the application sentence in the following unsaturated-cycle subsection. None of the earlier 128 statement blocks changes. The current source has 130 blocks, 190 unique labels, no unresolved cross-references, and identical bytes in the existing editor and repository files.

**Verdict:** the added criterion is correct under its stated hypotheses, and no correction is required. It concerns a fixed finite directed graph with a nonempty family of positive-length simple directed cycles, rational weights and a nonnegative edge bonus. Finiteness gives attainment of the new minimum. Every new cycle average is at least its old average, which is at least the old minimum. Equality of minima therefore forces an old critical cycle with zero total bonus; nonnegativity forces every edge bonus on that cycle to vanish. Conversely, such a cycle still attains the old minimum. Hence strict increase is equivalent to positive total bonus on every old critical cycle. The nonempty-cycle hypothesis excludes an undefined minimum. The definition of a directed cycle supplies its positive length.

The seven `BonusCriterion.lean` statements match the ingredients of the written argument:

- `finite_minimum_exists` supplies attainment for a nonempty finite cycle-index type.
- `mean_non_decreasing` derives monotonicity from the old lower bound, nonnegative average bonuses and attainment of the new minimum.
- `equality_iff_unaffected_critical` uses the lower-bound and attainment hypotheses for the new minimum and characterizes equality by an old critical index with zero average bonus.
- `strict_iff_all_critical_affected` gives the strict version under the same hypotheses.
- `nonnegative_sum_zero_iff`, `average_bonus_zero_iff` and `average_bonus_nonnegative` justify passage between individual edge bonuses, total bonuses and average bonuses. The division statements retain a strictly positive cycle-length hypothesis.

These are abstract rational cycle-family implications. Their instantiation to the graph is explained in the paper; this addition does not introduce a checked concrete graph construction or establish the remaining graph-to-snake correspondence. The paper describes the checked implications at that scope. Its unsaturated-cycle application is valid because the previously displayed attaining cycle lies entirely in the zero-bonus subgraph under the specified bonus restriction.

The explanatory paragraph explicitly separates strict finite-mean improvement from the sufficient numerical margin for 234, the potential-range bound and validity of the proposed shares for actual snakes. Therefore no claim that any strict improvement reaches 234 is made. Alternative bounds on the same five centres are combined by their maximum before taking the resulting edge-weight increment; the text does not add overlapping alternatives. These qualifications are necessary and are present.

The saved `data/bonus-audit.json` has SHA-256 `dbffea759a9ca9504bc5de7fbe5970594109df3e5986b7508da0b2bd096a8bea`. Its successful seven standard-axiom audits and log were inspected. All three saved byte hashes match:

- `lean/BonusCriterion.lean`: `9b1fe6c306300e3ab2a56c07d1979fa1f6a3ef054475451589824e2ab596cf2a`.
- `build/BonusCriterion.olean`: `b39ba7fc369d9b34882237a60197978e21a627af1e54cefadb596c107a89912e`.
- `logs/BonusCriterion.log`: `b48046bb3fb45cf6ba6e860212fddd809f702e5f784ec73d9703a811439f8674`.

Together with the seven earlier checks, this gives fourteen new audited statements. No Lean compiler, solver or LaTeX compiler was run by this reviewer. The earlier compilation and global-proof limitations remain unchanged.
