# Exact finite audit of the rounding-loss target

The audit independently enumerates all 4,608 coordinate squares in Q9,
counts each empty square at its four corners, and computes selected-neighbour
degrees at all 512 vertices. It checks the exact share identity and the
proposed degree decomposition at every corner of every audited selected set.
No SAT solver or Lean compiler was used. These are finite integer checks.

## Genuine snakes

The explicit 191-edge witness has total loss 163, all from degree-five
corners. Every one of the 131 bank paths was checked for distinct vertices
and induced consecutive adjacency. Their losses range from 152 to 913,
with total 25,668. This reproduces the older milestone27 bank aggregate
from a separately implemented square enumeration. It provides no lower
bound for unknown longer snakes.

## Existing dense cycle unions

The archived 208-vertex configuration consists of eight induced 26-cycles;
its loss is 256, split as 176 from degree five and 80 from degree seven.
The archived 224-vertex configuration consists of sixteen induced14-cycles;
its loss is 320, entirely from degree seven. Both were rechecked for their
selected degrees and connected components. Neither is a snake, and neither
falsifies the proposed loss-at-least-four condition.

## Exact zero-loss countermodels

A two-bit parity check with columns (1,1,2,2,3,3,3) on the first seven
coordinates leaves two free coordinates. Selecting syndrome zero gives
128 vertices, forming 32 induced squares. All 512 selected-neighbour
degrees are either two or three, so every remainder is zero.

Removing vertex zero leaves 127 selected vertices: one three-vertex path
and 31 induced squares. There are exactly two selected vertices of degree
one; every other selected vertex has degree two. All ambient degrees are
one, two or three, and the total loss is still zero. Thus the selected-degree
restriction together with exactly two endpoints does not force positive
loss if cycles and disconnected components remain permitted.

Alternatively, remove one corner from each of the 32 squares. Choose its
two free bits to encode the parity of bits zero, two and four, with the
second free bit zero. This produces 32 disjoint three-vertex induced paths,
96 vertices in total, and zero loss. The set is acyclic but has 64 endpoints.
Acyclicity alone does not force positive loss.

The parent's rank-four construction was also checked: columns
(1,2,3,4,5,8,9,12,13), selecting syndromes zero, one and two. It gives
96 vertices, sixteen induced six-cycles and zero loss. Its ambient degree
histogram is {1:192, 2:288, 3:32}. This confirms the same obstruction without
selected squares. The explicit selected sets are saved in results.json.

None of these is a connected snake, and all these degree-restricted
countermodels have fewer than 235 vertices. They do not refute the intended
statement about hypothetical snakes with at least 235 edges. They identify
which discarded global conditions must be restored before claiming a
positive loss lower bound.

## Exact small-loss restrictions

For degree five, empty-square counts zero through six give residues
0,2,4,1,3,0,2, respectively. Hence total loss at most three forces every
undominated corner to lie on no empty square, every degree-seven corner
to lie on no empty square, and excludes degree-five corners with exactly
two empty squares. At most three degree-five corners can have a positive
remainder. Degree-five corners with exactly five empty squares contribute
zero; replacing the residue by twice the empty-square count is invalid.
These consequences are mathematical deductions from the nonnegative
summands; this experiment does not present them as new Lean theorems.

All scripts and outputs are confined to this experiment directory.
Input hashes, exact histograms and resource-small execution time are saved
in results.json. The universal loss bound and the Q9 optimum remain open.
