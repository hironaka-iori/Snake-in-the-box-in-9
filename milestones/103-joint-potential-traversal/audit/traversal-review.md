# Joint traversal review

A separate read-only source review found no discrepancy in the digit schedule
or the one-way implication to the original prefix checker. This review supplies
supporting analysis; the successful Lean receipts establish the checked claims.

For the six successive digit positions, the source selects widths
1296, 216, 36, 6 and 1, then retains its last subtree. The target retains its
initial subtree at the first position, then selects those same five widths.
This agrees with the existing source offset given by the quotient by 6 and
target offset given by the remainder modulo 7776.

A rejected acceptance branch returns success immediately. A nonzero branch
with a mismatched potential-node width returns failure. Thus the new checker
can be stricter on malformed inputs; only the implication from its success
to the original check is used. Constant leaves remain valid at every depth.
An accepted terminal above depth zero still expands the remaining digits.

The general proof covers early constant leaves, terminal acceptance above
depth zero, rejected branches, the last digit and the first-digit delay.
The original minimum with the profile's range bound is retained at each
accepted leaf. The finite comparisons include both profiles and the context
99/37, whose count-dependent credit is active.

No claim about arbitrary snakes follows from the traversal theorem alone.
Every assigned graph context must still be covered, and the global catalogue
and conditional local-share premises remain separate obligations.
