# Milestone 127: direct count clauses and two unresolved searches

The generic lower-count/direct-clause equivalence passed Lean with five
dependency reports. All 235 concrete clauses were independently derived from
the unchanged 106348-clause input by 132921 checked propagation references.
No new definition, six-count floor or global upper bound is claimed.

A second input replaces six lower-bound counter families with these clauses.
It has 101666 clauses and 4820 occurring variables, preserving the original
variable numbers and a complete map back to the original inputs. A separate
review explains the sound RUP proof transport. The first 1000 deductions from
both native traces have passed that transport check; this is not a complete
contradiction replay.

Both changed encodings timed out after 180 seconds. No model or contradiction
was obtained. The raw partial traces are retained locally and losslessly
archived; their redundant raw copies are excluded from the repository manifest.
The retained range is 191–235 with the documented upper-proof rebuild limitation.
Conditional 234, the optimum and 196 remain unresolved.

Read [the mathematical note](MATHEMATICAL_NOTE.md),
[independent prelude review](audit/prelude-review.md),
[counter equivalence and Lean receipt](audit/direct-cardinality-derivation.md),
and [reduced-input proof transport](audit/reduced-encoding-review.md).
The next focused task is `data/next-pair-task.json`: expose the already-proved
second/fourth count sum at least 8 using all 42 corner occurrences, with the
new counter semantics checked explicitly. That input is not implemented.

The manuscript remains revision 126, unchanged and identical to the open
editor source. The next scheduled full paper revision is 136. Active 104/115/122
drivers were observed and left unchanged; check live processes before resuming.
Run `scripts/verify_saved.py --verify` to check this saved checkpoint.
