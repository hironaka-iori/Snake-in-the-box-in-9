# Verification scope

The proof checks use Lean 4.19.0 and the previously checked project dependencies. The full inherited dependency closure is not rebuilt in this milestone. Each new successful receipt records the exact source, output object, compiler log, checker snapshot and direct dependency hashes. Printed theorem axioms must be a subset of `propext`, `Classical.choice` and `Quot.sound`. A source containing a proof placeholder or `native_decide` cannot receive a successful receipt.

The 46 ported sources retain their original non-import bytes, except for the exact namespace substitution `CountPropagation65` to `CountPropagationPort95`. Eleven files use that substitution, including eight selected capped theorem names. The root byte audit independently checks the transformation. The port plan retains original sources, historical receipts, all import replacements and the transformed declaration names.

The declaration scan found five conflicts between the old count support and the current history support: `known_absent_count`, `corners`, `corners_count`, `canonicalCentres` and `centresOf_canon`. A consistent namespace change preserves both sets of declarations. No conflicting declaration was discarded. The scan is a source check; successful compilation in the combined environment supplies the decisive compatibility check.

The first pilot attempts are retained. Two failed during import resolution: one lacked the graph's support paths, and the next selected an older directory for the `LocalWindowSat` module prefix. The final path order preserves the defined graph's support-directory precedence. A subsequent pilot attempt exposed two proof-elaboration errors involving an implicit path length and an equality substitution. Explicit introductions and a directed rewrite resolved them. Only the later successful pilot receipt is evidence for its theorem.

The independent literal audit compares all 55 generated rules, 69 geometric adapter statements and eight capped adapter statements with milestone 94's pinned rows. It also checks rule order, caps, credit values, original model indices and edge numbers. This data comparison does not replace the Lean proofs.

The first final-assembly attempt left the impossible empty-list membership case unsimplified after splitting the 55 alternatives. The repaired generator explicitly simplifies empty-list membership and disjunction with false. The prior generator, generation receipt, failed source snapshot and log are retained. No rule, cap, credit or theorem statement changed in this repair.

The final history-credit theorem has only the snake and window-fit hypotheses once every concrete rule is supplied. Importing the defined graph checks that these results coexist in its proof environment. It does not discharge the defined graph's separate retention premises or verify its complete numerical potential.

The port manifest describes prepared sources, and the generation receipt describes generated adapters. Their status names intentionally do not assert compilation. Successful module receipts and the final proof summary determine completion. Failed logs, timeouts and uncompiled sources remain distinguishable from completed checks.
