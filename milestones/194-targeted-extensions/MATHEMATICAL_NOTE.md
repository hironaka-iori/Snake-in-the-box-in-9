# Round 194: targeted extensions and a lower-dimensional comparison

Every single length-preserving contiguous replacement of at most 44 edges in the 131 saved 191-edge Q9 snakes, followed immediately by one endpoint addition, is computationally excluded. This is distinct from round 193's closure under arbitrarily many moves of at most33 edges. It does not exclude sequences of larger replacements.

The main comparison is in Q7. The specific 48-edge lift of the optimal26-edge Q6 middle is globally suboptimal because a50-edge Q7 snake is known. Nevertheless, one replacement followed by endpoint addition cannot improve it to 49 when the block has at most 37 edges. An explicit aligned subpath of the known 50-edge snake gives a49-edge construction using a43-edge replacement. Thus the minimum block length for this operation lies in [38,43]. Its exact value remains unresolved. Both the old48-edge and new49-edge paths, and their retained positions, have now passed Lean checks. The numerical lower cutoff remains native.

## Search and pruning argument

For a specified candidate new endpoint w, remove every original blocker inside the replacement interval. The new interior avoids retained vertices, neighbours of retained nonanchors, w and all neighbours of w. The two anchors are restored only after verifying that all original blockers, except the endpoint to which w attaches, lie strictly inside the interval.

A nonanchor vertex with at most one available neighbour cannot belong to a simple path between the anchors: each internal path vertex has two distinct neighbours on that path. Repeating the deletion preserves all possible routes. The anchors must remain connected, and their graph distance cannot exceed the required length. Component size and bipartite colour counts give further necessary bounds.

For equal-coloured entry and exit, with t edges-pairs, the route uses t+1 vertices of the starting colour and t of the other. Its edge bound is twice the smaller of the available starting-colour count minus one and the other-colour count. For opposite colours it is twice the smaller colour count minus one. These arithmetic implications pass Lean under their count premises.

The allowed graph can also be decomposed into biconnected blocks, with bridges treated as blocks. Only the blocks on the terminal-to-terminal route can be used: entering an attached branch and leaving it repeats its cut vertex. If a used block's entry and exit are adjacent, inducedness forces their edge directly; any longer local route has that edge as a chord. Sum the local colour bounds, using one for adjacent entry/exit. Lean checks the single-attachment contradiction and the adjacent-anchor implication. The graph decomposition algorithm and its complete transfer remain written/native evidence.

Unresolved queries were converted to exact selected-vertex count and induced-degree models, with fixed anchors, colour counts and all contained square exclusions. The initial relaxation permits disconnected longer cycles. Every observed such cycle gives a valid exclusion of selecting all its vertices together. Initial models and subsequent cycle cuts are both retained. No solver INFEASIBLE result is presented as a Lean contradiction certificate.

## Evidence and limits

The baseline covered lengths 34--42. Its512 unresolved queries at 36--42 were all excluded by 373 distinct solver models in 13.297 seconds. A further reduced-node scan visited lengths 43--51; the solver revisit of 43--45 advances the complete cutoff to 44. Later unknowns, unvisited queries and the globally interrupted active query remain unresolved. Completion.json records coverage by length.

The lower-dimensional scan excluded lengths 2--27 directly and 28--32 after171 solver retries. The next solver pass advances the complete lower cutoff to 37. Of576 isometric placements of known 49-edge subpaths with the desired48-edge tail anchors, the best displayed placement changes the block from position0 to 43. Its coordinate map and translation are saved with the full vertices. This576-placement search does not classify all 49-edge snakes.

The demonstrated lower-dimensional obstruction is compatible with suboptimality. Therefore the Q9 local exclusions do not support an optimality claim for 191. The next constructive route is to reroute the 231 shortened189-edge states from round 193 before regrowth, beginning with the 11 classes that already permit one endpoint addition. That operation has not yet been examined.

The two manuscripts are updated in place, preserving the authors and local hyperlink settings. Archived 235 retains its pending independent-rebuild qualification;233/234 remain conditional. The contributor head at the opening fetch was aeab10ecbab6480a11f927e590b664bd7f0b4f5f, unchanged from round 193. Whole-manuscript consistency review remains scheduled for round 200. The goal remains active.

Publication fetch: the contributor branch advanced to ecc47830c77df280f402f851799336dc81a7f680, reporting 2659 of 3118 production modules. The diff is saved in milestone194 data/contributor-final.diff. It was neither merged nor independently rebuilt.
