# Next construction-consistency question

Stop after round 239. The following is a saved proposal for a later explicit resumption, not a completed search.

The next unrestricted recovery question is whether five missing neighbour counts can conceal a change in a binary selection. The working conjecture is that any nonzero ternary selection difference changes at least nine neighbour counts. The proved written lower threshold after this round is five; the one-vertex example attains nine. The conjecture remains unresolved for supports of sizes five through eight.

The new results substantially reduce the five-position question:

1. Mixed-parity supports split into two blocks, each of size at most four. The four-erasure theorem excludes them.
2. A support with no distance-eight pair is excluded by the conditional eight-erasure theorem.
3. Thus only five same-parity positions containing a distance-eight pair remain. Translate one endpoint to zero and permute coordinates so that the other is 255, the vector with its first eight bits set and last bit zero.
4. Describe the other three vertices by the eight possible column patterns on the first eight coordinates. Their multiplicities are nonnegative and sum to eight. There are exactly C(15,7)=6435 descriptions. Each vertex's last bit is forced by its required even parity. Exclude repeated vertices. This covers all remaining cases; it does not claim 6435 distinct isometry classes.
5. Canonicalize the ten pairwise distances, construct the five-by-five antipodal matrix, and examine the 243 ternary right-hand sides by exact integer arithmetic. Any singular matrix requires separate bounded integer analysis; it must not be discarded or treated as an infeasibility result.

Every actual neighbour-sum difference lies between -9 and 9. A surviving matrix solution is only a necessary condition. Apply the full inverse at all 512 vertices and require every selection difference to be -1, 0 or 1, then compute all neighbour sums directly. A validated survivor would refute five-count recovery. It would not itself construct a snake, since connectedness and induced-path degrees remain additional requirements.

If all cases are excluded, the unrestricted recovery threshold increases from four to five missing counts. If only the antipodal calculation is inconclusive, use further inverse rows before abandoning the question. No success or running-time improvement is asserted in advance.

A separate proof-assistant priority is to connect the geometric classification to the actual cube and combine it with the 87 accepted matrix theorems. The fully assembled Lean recovery theorem currently covers three missing counts. The conditional eight-count argument has checked scalar/list arithmetic with its cube interpretation still written.

This route supplies necessary consistency conditions for constructing a longer snake. It gives no snake-length upper bound and does not duplicate the collaborators' global upper-bound work. The open majority exchange family still removes two old vertices and inserts three; the four-minority-replacement cases and frozen earlier searches retain their saved statuses.
