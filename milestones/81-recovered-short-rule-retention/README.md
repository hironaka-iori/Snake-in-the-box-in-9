# Milestone 81: preservation under forty recovered local filters

The forty local filters recovered in milestone 70 now have a combined Lean
theorem showing that every eligible window of an actual snake survives them.
This closes the short-rule part of retained-edge interpretation. The maintained
project interval remains **191 <= a(9) <= 235 edges**. The target 234 still
requires five local share targets and the remaining graph and potential proof.

## Precise result

Let a snake have m edges, and let r+9 <= m. Its six stored count symbols are
the singleton counts at r+3 through r+8, each truncated at six. For each of
the forty listed rules, choose either orientation and an offset fitting its
direction word inside the nine-transition window. If every tested position
lies among those six stored positions and the canonical direction word
matches the rule, its encoded forbidden condition is false.

The theorem `Snake9.ShortRules81.all_short_rules_retained` has no unresolved
local-refutation premise. The catalogue contains 37 component-cap rules and
three sum rules. The component caps are strictly below six. A sum test applies
only when each participating symbol is below six; the value six represents
the interval [6,21] and cannot be substituted for an exact count in such a sum.
The three sum lower bounds are 5, 6 and 13, with forbidden caps 4, 5 and 12.

The proof covers coordinate relabelling, reversal and all valid placements.
Unrepresented internal counts in the longer local certificates use the
universal ceiling 21. Thus the theorem does not require seven internal counts
to fit into six stored positions.

## Evidence

Eight modules passed Lean 4.19.0, with 66 printed theorem audits. Only
`propext`, `Classical.choice` and `Quot.sound`, or subsets, occur in these audits.
Five modules assemble the new transfer and catalogue results; three small
semantic support modules were copied exactly and checked again. A further
970 existing certificate objects were reused with pinned source and object
hashes. This round did not rebuild the entire inherited dependency closure.

The executable comparison extracts the actual short-rule loop from the
milestone-70 builder. It reconstructs its inputs from the current source
cases, checks them against the saved builder metadata, and independently
parses the literal Lean catalogue. All 505 direction shapes and 46,656 count
codes agree: 23,561,280 pairs and 7,927 applicable rule placements. This
isolated family retains 9,102,995 pairs and rejects 14,458,285. These totals
are not numbers of newly removed edges in the complete graph.

The resulting mask has SHA256
`1ff64848a9814704b92da43de676f5b2e75145315bdd7450d8fa46734acd9e94`.
The checker pins its code, the builder, saved input model, direction table,
source cases, normalized rules and Lean catalogue sources. It is a separate
exhaustive Python comparison; Lean does not encode Python execution here.

Independent source and receipt review is in
[audit/final-review.md](audit/final-review.md). Exact successful receipts,
support provenance and comparison results are in `data/`. The
[checkpoint](data/checkpoint.json) and [file manifest](data/file-manifest.json)
identify the saved evidence.

## Reproduction

Use the Python and Lean 4.19.0 paths documented in
[the handover](../../handoff/CURRENT_STATUS.md). From the repository root:

1. Run `scripts/prepare.py` in this milestone to validate prior source receipts,
   recreate the certificate overlay and regenerate the two catalogues.
2. Run `scripts/check.py MODULE` in this order: `PositionTransfer`,
   `GuardTransfer`, `JointCountBridge`, `JointCountTags`, `MultiCentreCount`,
   `CapCatalogue`, `SumCatalogue`, `ShortRetention`.
3. Run `audit/check_builder.py` to repeat the complete isolated-filter comparison.
4. Run `scripts/finalize.py` to verify source, object, log, dependency and input
   hashes and save the summary. Run `scripts/verify_saved.py --verify` to
   check the frozen file manifest; changed receipts require a new manifest.

The scripts depend on pinned local support caches and absolute runtime
paths. On another host, restore or rebuild those dependencies and adapt the
paths before claiming a reproduced check. The manifest is an integrity record,
not a standalone proof checker.

## Remaining obligations

The exact graph still needs the 1,378-key reference union, three history
exclusions and retained-array membership. The ten completed interval filters
were connected to actual snakes in milestone 79; the forty short filters are
connected here. Every compatible eleven-direction interpretation of a
three-ID credit must then be covered, followed by complete potential replay.

Case 7305 is already complete and integrated. The five remaining local share
targets are 7301, 7302, 7303, 7307 and 7308. The checked-local-share finite
comparison remains mean 483 and potential range 551, giving integer comparison
235. The full proposed catalogue gives mean 496 and range 600, with conditional
target 234. These assembly checks establish neither the exact optimum nor a
196-edge construction.

The paper remains revision 76. Its existing editor and repository sources are
unchanged and hash-identical; the next scheduled full revision is 86. No new
PDF compilation or layout result is claimed by this milestone.
