# Milestone 84: three-history retention

Every actual snake passes the three history-exclusion tests in the current
comparison graph. Eight modules passed Lean 4.19.0 with 38 theorem audits.
The final retention theorem has no unresolved local-certificate premise.
This closes one component of graph interpretation; it does not change the
project interval of 191 through 235 edges or establish the conditional 234 bound.

## Statement and proof

At graph step r, the stored history describes preceding nine-direction windows.
If a three-entry signature is emitted, then r is at least two and its entries
are exactly the direction IDs at r-2, r-1 and r. Hence the signature describes
three overlapping nine-direction slices of the actual eleven-direction word
beginning at s=r-2. No three-entry signature can be emitted at the first two steps.

For the three exclusion signatures, the compatible canonical induced word is
unique. The existing count inequalities then give:

| Signature | Canonical eleven-direction word | Required singleton count |
| --- | --- | --- |
| 139, 353, 177 | 01230432543 | \(\alpha_{s+10}\ge3\) |
| 460, 350, 180 | 01234532013 | \(\alpha_{s+8}\ge3\) |
| 460, 353, 177 | 01234532053 | \(\alpha_{s+10}\ge3\) |

The six stored count symbols at step r represent positions r+3 through r+8.
Thus the relevant digits are respectively 5, 3 and 5, using zero-based indices.
Each digit is min(6,alpha), so the count lower bound three makes the builder's
guard "digit at most two" impossible. This proves retention for every fitting
step of every snake, including the early-step boundary through the no-emission
argument. No assumption about the snake's total length beyond a fitting window
is added.

The count inequalities come from milestones 65 and 66. The new work is their
complete connection to the three history signatures and encoded guards. No
claim of novelty outside this project is made.

## Completeness and verification

The finite uniqueness proof fixes the first nine canonical directions and
checks all 81 possible pairs of remaining labels below nine. Restricted-growth,
induced-path and overlapping-window conditions filter these continuations.
Lean proves that the actual eleven-direction window lies in this enumeration.
It therefore covers every compatible word, rather than relying on a selected
representative.

A separate Python enumeration generates all 11,162 canonical induced
eleven-direction words in nine coordinates. It agrees with the prefix checks
and finds one compatible word for each of the three signatures.

The exact history-filter loop is extracted from the current graph builder.
It agrees with the Lean rule literals on all 37,875 history/direction pairs,
using six uniform count vectors to expose every possible active signature.
The three active pairs are then checked on all 46,656 six-count codes each:
139,968 additional tests. Each isolated guard rejects 15,552 count codes.
These are isolated filter counts, not numbers of newly removed full-graph edges.
The executable comparison is separate from Lean's proof; the Python interpreter
is not encoded in Lean.

All 38 theorem audits contain only `propext`, `Classical.choice` and `Quot.sound`,
or subsets. The inherited window and direction environment is reused with
source/object/log checks. Its complete dependency closure was not rebuilt.

## Compatible count-proof replay

The original count-proof imports brought in `ShareFrame`, which duplicates
declarations already supplied by the current `LocalWindowShareBridge`. That
import attempt failed and is retained as a diagnostic.

The successful preparation copies the five required helper theorem bodies and
their definitions from milestones 58, 62 and 65 into `HistoryCountSupport`.
Only imports and namespace placement change for these helpers. The three count
proof modules retain every original definition and proof body; their import is
replaced and an unused namespace-opening command is removed. All four adapted
modules are checked afresh in the current environment. The source-extraction
receipt identifies the original and adapted hashes.

The files under `diagnostics/` describe the rejected original import approach.
Its preparation script is preserved as historical source and must not be run
to prepare this checkpoint. The active preparation script is
`scripts/prepare_compatible_counts.py`.

## Reproduction

From E:/Snake-in-a-box, use the saved Python runtime and Lean 4.19.0 environment:

1. Run `scripts/prepare.py` to pin the three patterns and generate the finite tables.
2. Run `scripts/check_history.py` for the generic history/window bridge.
3. Run `scripts/check.py HistoryRealizations`, then `scripts/check.py HistoryUnique`.
4. Run `scripts/prepare_compatible_counts.py`, then `scripts/check.py` for
   HistoryCountSupport, TerminalCount, CountPhase04 and CountPhase29 in that order.
5. Run `scripts/check.py HistoryExclusions` and `audit/check_builder.py`.
6. Run `scripts/finalize.py`, then `scripts/verify_saved.py --verify` to check
   an existing frozen manifest. Changed receipts require a new manifest.

The scripts use pinned local support and absolute runtime paths. Another host
must restore or rebuild that support and adapt paths before claiming reproduction.
Build caches remain local. Sources, successful receipts, logs, provenance,
independent review and the exact current handover are preserved.

## Remaining work

Full retained-edge membership still requires the 1,378-key reference union and
the exact retained-array index. The ten interval filters, forty short filters
and three history exclusions are now connected to actual snakes. Credit
interpretation for every compatible eleven-direction realization and the full
potential replay remain separate obligations.

Case 7302 continues under its existing proof driver. Its local share theorem is
pending until refutation replay, geometry, reversal and the final audit finish.
No duplicate driver was started. Its single-premise mean 9259/19 still gives
conditional integer comparison 235. All five pending target local shares remain
explicit. The maintained upper bound 235 uses the inspected contributor theorem
and saved audit, without a fresh complete independent rebuild.

The paper remains revision 76. The editor source, repository mirror, authors
and hyperlink settings are unchanged; the next full revision is scheduled for 86.
