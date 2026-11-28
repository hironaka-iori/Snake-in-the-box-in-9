# Round 279. Exact completions of the first 134 edges of archive path 191-0

The maximum length of a snake containing vertices 0 through 134 of archive path `191-0` as a consecutive interval is **191 edges**. Indices are zero-based. For the fixed, directed, literal interval there are exactly two maximum completions. They represent bank entries 0 and 1. The same maximum and the same two completions hold for each longer prefix through index 153 because both literal completions contain that 153-edge prefix. Reversal and cube symmetries give equivalent statements in other positions.

## Why both ends were covered

For a proposed first step from the left tip in bit direction $d$, another retained vertex equal or adjacent to that proposed vertex blocks the step. In bit order 0 through 8 the earliest blocking indices are 1, 4, 12, 16, 2, 128, 16, 18 and 66. Consequently the left tail has length zero whenever the first 128 edges remain fixed. At 127 edges the step flipping bit 5 becomes legal. Later choices at the other tip can only remove available steps.

The archived donor supplies 38 edges beyond the literal 153-edge prefix. Two single-tail traversals found maxima of zero and 38. Removing its last edge gives zero and 39 at length 152. We then enumerated both tips, using occupied-neighbour counts in one order and availability masks in the opposite order. At retained length 134 their counts agree at **every** final length, including exactly two at 191. Each saved maximum path was also checked by comparing all vertex pairs.

The enumeration at length 128 reached its work allowance. The original donor still gives a lower bound of 191 there. The shorter prefixes require a different calculation to settle target 192.

[Targeted prefix and original donor](prefix.json) ﾂｷ [Length counts, literal completions and blockers](spectrum.json) ﾂｷ [Enumeration and replay](spectrum.py) ﾂｷ [Resource receipts](runs)
