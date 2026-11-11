# Dimension lifting: round 188

The current direction is constructive, following the user's request to study 6→7, 7→8 and 8→9. The equalities 50=2·26−2 and 98=2·50−2 motivate 194 as a provisional construction target. No recurrence or optimum is proved.

## Exact mathematical result

For three induced base paths P,Q,R, require P∩Q and Q∩R to consist exactly of their respective joining endpoints; require P,R to be disjoint and nonadjacent. Placing P,R in one face and Q in the other produces length |P|+|Q|+|R|+2. TwoCrossings188 checks this for a general graph product. Reconstruction7188 checks the actual Q6 components of lengths 18,24,6 and their compatibility, giving 50 edges in Q7. Length means number of edges.

Published representatives have minimum-crossing decompositions:

| Dimension | Edges | Crossings | Component edges |
|---|---:|---:|---|
|6|26|2|2,13,9|
|7|50|2|18,24,6|
|8|98|4|8,25,10,25,26|

Deleting q crossing edges leaves q+1 induced components. Their lengths sum to m−q. Same-face components are disjoint and nonadjacent. Opposite-face intersections occur exactly at crossing ports. The Q8 representative has a face containing two 25-edge paths (52 vertices), so a face cannot be bounded by a single Q7 snake. The representative-specific crossing obstruction is invariant under cube symmetries and reversal; no claim about all optimal snakes is made.

## Relation to the saved Q9 bank

All 131 saved 191-edge snakes were checked pairwise and projected along every coordinate. Minimum crossing counts: 25 have one, 88 have two, 12 have three, 6 have four. The one-crossing cases split 96+94+1.

There are 88 two-crossing cuts. Their middle paths have three symmetry types: 84 copies of a 95-edge type, two of a 93-edge type and two of a 92-edge type. Transition normalization over both orientations proves none is a contiguous subpath of the displayed 98-edge representative up to translation and coordinate permutation. These are native finite-data calculations, not a Lean classification.

The common middle path splits 31+47+15+2=95. The outer Q8 components in each corresponding Q9 witness sum to94, giving191. This makes compatibility and endpoints more informative construction data than the scalar maximum alone.

Every cube edge flips Hamming-weight parity. Fixed endpoints therefore force replacement length parity. PortParity188 checks the general alternating-colour deduction; the cube-colouring application is the elementary written argument. A fixed-port95→97 replacement with the surrounding components retained would give193. For194, a possible length allocation is97 in the middle and95 total outside. Neither configuration has been found.

## Searches and exact scope

The original opposite-face model requires nontrivial outer components. It reconstructs50 with a fixed24-edge Q6 middle (OPTIMAL), reports INFEASIBLE for a fixed published50-edge Q7 middle targeting98, and returns UNKNOWN after120 seconds for the common95-edge Q8 middle targeting192. The last result gives no exclusion and no new witness.

Review found that singleton outer paths must also be allowed for the full two-crossing family. The original model and outputs are preserved. The corrected model allows degree zero at either crossing port and retains the two-component forest constraint. Repeating the fixed50→98 query with this corrected model reports INFEASIBLE in22.875 seconds. This is a restricted solver result without a Lean refutation. The original Q9 run was not repeated; its recorded scope remains nontrivial outer components.

The model uses induced edge variables, maximum degree two, flow from the two ports to every selected vertex, and |E|=|V|−2. Flow excludes a component without a port. Degree and edge count then force two paths, each with one port. Only feasible decoded witnesses receive independent all-pairs validation. Solver infeasibility is not a general-dimensional upper bound.

## Verification and limitations

The generic joining result, direct Q6 and Q7 witnesses, concrete Q6→Q7 reconstruction, Q8 transition sequence, its minimum crossing count and cut positions, and alternating-colour parity have accepted Lean receipts. The direct full Q8 all-pairs recheck remains incomplete under the unchanged256MiB per-worker limit. Its native all-pairs verification passed. Failed finite-proof attempts and exact sources remain in logs; accepted proofs are immutable. This does not affect the accepted generic joining theorem or concrete Q7 reconstruction.

The inherited interval is191–235, with the archived235 proof's complete independent rebuild pending. Conditional233 and234 chains retain their documented assumptions. No new record, improved global bound, or proof of196 is claimed. The manuscript-wide review remains overdue and pending.

## Next research step

Search for a97-edge replacement between the two ports of the common95-edge middle path while fixing the two outer Q8 components. Every interior vertex of the new middle path must avoid the outer vertex sets, and the only projected overlaps must remain the two ports. A solution gives193; a certified exclusion rejects only that fixed context. If excluded, vary the outer components and ports, using the three-path compatibility rule. Do not repeat the unchanged120-second query or assume the published98-edge path is a useful seed.

## Sources

- Transition catalogue: https://minortriad.com/snake/ (exact HTML saved, accessed11November2026).
- Taylor, compatible path lifting: https://arxiv.org/html/2609.27483 .
- Orland et al., record construction context: https://arxiv.org/html/2607.15270v3 .
- Existing local bank: work/bank9.json; exact SHA is recorded in data/completion.json.

No novelty claim is made for the general lifting method.
