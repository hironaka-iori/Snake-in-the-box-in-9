# Milestone 125: retained empty squares and a critical six-count restriction

Read [the mathematical note](MATHEMATICAL_NOTE.md) for the deductions and their
limits. Lean checks a stronger necessary shortfall condition for snakes of at
least 235 edges, conditional length bounds retaining empty squares, and the
six interval restrictions for a total-at-most-22 window of shape 0120324.

The three native searches timed out. No new local floor or unconditional
length bound is established. The [search review](audit/search-review.md) and
[bounded search review](audit/bounded-search-review.md) preserve that distinction.
The [proof review](audit/proof-review.md) and
[supplement](audit/proof-supplement.md) cover three modules and 19 reports.

The next proposed encoding change is saved in `data/next-encoding-task.json`.
The partial solver traces are archived losslessly; the archive metadata records
how to restore the uncompressed files before rerunning the search auditors.
The paper remains revision 116, with the next full revision due at 126.
