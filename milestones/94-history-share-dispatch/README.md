# Milestone 94: complete history-share configurations

All 73 Lean theorem audits passed. This milestone classifies every compatible canonical eleven-direction configuration for all 55 saved history share signatures and connects emitted signatures to actual snake windows. The successful Lean modules and remaining assumptions are recorded in `data/checkpoint.json`.

There are 69 configurations: 41 signatures have one configuration and 14 have two. All eight older representative-only rules are unique. The 47 later variant lists agree with complete reconstruction. Two numerical enumeration methods agree: all 11,162 canonical induced eleven-direction words and 81 continuations per signature.

The [mathematical note](mathematical-note.md) defines compatible configurations and explains the centre positions. The generic credit statements retain a geometric bound for every compatible word. Numeric caps transfer only when strictly below six; the saturated symbol remains an interval.

## Sources and checks

- `HistoryShareCover.lean`: finite coverage extraction and actual-window dispatch.
- `ShareCover00.lean` through `ShareCover10.lean`: all 55 finite coverage certificates.
- `HistoryShareAssembly.lean`: ordered all-rule assembly and actual emitted-window membership.
- `HistoryShareCaps.lean`: numeric cap transport and capped share dispatch.
- `HistoryShareValidity.lean`: validity of every listed configuration and exact compatible-set characterization.
- `HistoryShareCounts.lean`: distinct signatures and the exact counts 55, 69, 41 and 14, together with the assembly's length theorem.
- `data/variants.json`: original rule indices, signatures, configurations, caps and credit values.
- `audit/credit-provenance.md`: existing local-credit sources and transfer obligations.

The checker uses Lean 4.19.0, runs modules sequentially and audits the printed axioms. Existing dependency objects are reused with source/object/log pins; their entire closure is not rebuilt. `scripts/verify_saved.py --verify` checks the frozen manifest.

The next task is to instantiate the geometric and capped bounds in one compatible proof environment, then combine applicable credits by maximum. Old and current modules declare the same core share name, and several old instance-module names also collide. The inspected core share definition text agrees; module ownership still prevents direct import-path combination. One legacy uncapped credit also needs a nine-direction suffix transfer.

The interval remains $191\le a(9)\le235$ edges, with 234 conditional. The 235 upper bound retains contributor-proof and saved-audit evidence, pending a complete independent rebuild. The witness and geometry batches continue; case7302 remains stopped at its preserved Check1 timeout. Paper revision 86 and both source copies remain unchanged; the next scheduled full revision is 96.
