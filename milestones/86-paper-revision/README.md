# Milestone 86: revised paper and proof scope

The existing paper now incorporates milestones 77–85. Its main argument moves
from square incidence and local shares through the actual state sequence,
exclusion filters, finite comparisons and obstructions, followed by the precise
remaining requirements for a stronger global bound. The project interval
remains 191 through 235 edges; 234 is conditional and 196 remains unresolved.

## Mathematical changes

- The completed count-independent theorem includes the 012310 share bound 12.
  Five canonical shapes now have a completed bound; four meet their target
  floors. Five target cases remain pending.
- The completed-local-share comparison is mean 483 and range 551. The older
  480/536 comparison is labelled historical. The single additional 012034
  target gives mean 9259/19, range 11301/19 and integer comparison 235. The
  full proposed catalogue retains mean 496, range 600 and conditional 234.
- Four new propositions explain the actual direction/history/count sequence,
  interval and short-rule retention, the three unambiguous history exclusions,
  and reference-table retention under its two explicit catalogue premises.
- A fifth proposition states and proves why nonnegative bonuses confined to
  stored counts of six leave the completed graph's minimum mean at 483.
  The four-edge witness and its precise finite-model scope are included.
- A definition of critical cycles and the zero-bonus subgraph gives an exact
  criterion for improving the minimum cycle mean. A nonnegative bonus raises
  it precisely when every old critical cycle receives positive total bonus.
  This criterion is distinct from achieving the numerical bound 234.
- The abstract, principal-results table, comparison section, proof checklist
  and verification discussion now share the same evidence boundaries. The
  reference catalogue premises, retained-array membership, credit coverage and
  complete potential replay remain visible.

## Source and logic checks

The editor source is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`; the repository mirror
is `E:/Snake-in-a-box/paper/snake9_research.tex`. Their bytes match. The complete
preamble, all hyperlink settings and authors Iori Hironaka, Tommy Ma and
Steven Zhan are preserved.

There are 130 statement blocks: 122 previous blocks remain unchanged, the
existing count-independent share theorem is strengthened, and six propositions
and one definition are added. The entire original appendix body is unchanged.
All 13 printed paths pass 118,673 vertex-pair tests. All 190 labels and bibliography references
resolve, and the old 175-row exclusion table is preserved.

Fourteen new Lean 4.19 checks cover abstract cycle-family preservation under
nonnegative bonuses, sums of those bonuses, the three current conditional
budget implications, all four displayed comparison fractions, finite
minimum attainment and the exact bonus equality/strictness criterion. Only standard
axioms occur. Previous geometric and graph-interface receipts are reused after
source/receipt checks; the entire historical dependency closure is not rebuilt.

The built-in editor compiler failed before source compilation because its
Windows helper could not prepare the execution environment. The exact result
is saved in `data/editor-compile-final.json`; the first attempt is retained
separately. No new PDF or visual layout check is
claimed, and no separate document or PDF was created.

The independent pre-edit audit read the complete original paper. The post-edit
review checks all additions and changed statements against current evidence.
Its corrections to history notation and the exact signature equivalence are
incorporated. Source checks and review remain distinct from compilation.

## Reproduction and continuation

Use the saved Python runtime with `-X utf8` from the repository root.
`scripts/revise.py` reconstructs the revision from the exact baseline and
refuses to overwrite an unrecorded edit. The `text/` files supply the new
mathematical exposition. `scripts/check_logic.py` checks seven statements,
and the same script with argument `BonusCriterion` checks seven further
statements. `scripts/verify.py` checks preservation, witnesses, references,
arithmetic and reused receipt hashes. Runtime and inherited support paths
are host-specific.

`scripts/finalize.py` records the current paper and a frozen observation of
the active case7302 replay. Inspect its actual process before continuing; do
not duplicate the driver. Its clause interpretation has passed, while final
refutation replay, geometry, reversal and the complete local audit remain
pending. Case7305 is complete and must not be restarted.

The next proof task is exact retained-array membership, using the checked
candidate sequence and filter theorems with the two reference premises explicit
until their closed dependencies are available. Credit interpretation must then
cover every compatible eleven-direction realization. Completing only the
012034 floor still does not reduce the integer comparison below 235.

The next scheduled full paper revision is milestone 96. Shared current status
and continuation instructions are in `handoff/`; historical manifests preserve
their earlier versions.
