# Two simultaneous block replacements: prepared source

Status: source prepared only. No compiler, solver, native worker or software tests have been run. Compilation awaits the parent's resource-slot release and accepted dependency staging.

## Exact statement

`TwoBlocks224.firstIntermediate` takes two actual indexed induced paths `p,q` of the same edge length `n`. The first open index interval is `(a,b)` and the second is `(c,d)`, with `a<=b<=c<=d`. The paths agree at every index outside their union. For each first-interval index `i` and second-interval index `j`, assume `q i` differs from `p j` and there is no ambient edge from `q i` to `p j`.

The constructor returns an actual `InducedPath` of length `n`, with vertex `q i` inside the first interval and `p i` everywhere else. It introduces no mask, relation or closure definitions. When the anchors are path indices, agreement outside the two open intervals keeps every anchor unchanged. Empty intervals are harmless; the usual proper bounded intervals are a special case.

The separation hypothesis excludes both equality and adjacency. The ordering implies that a first-interval index and a second-interval index differ by at least two even when `b=c`, so their absence of adjacency is consistent with the required path-index condition. No symmetry assumption is necessary for the imported ordered-index path definition: the first-interval index always precedes the second-interval index in the only mixed adjacency case.

## Proof and existing work

Read the complete accepted `193-block-reroutings/lean/BlockReplacement193.lean`, including `replaceBlock` and `finiteChain`. The replacement constructor already proves inducedness from separately supplied within-block and boundary conditions; the new result derives the needed geometry from two actual whole paths. A direct pair split avoids restating those boundary conclusions as hypotheses and imports only `LayerJoining`.

For injectivity, two first-interval vertices use `q.distinct`, and two other vertices use `p.distinct`. For a mixed pair, an outside vertex in the second interval is excluded by the separation premise; any other outside vertex agrees with `q`, so `q.distinct` applies.

For induced adjacency, pairs wholly inside or outside the first interval use `q.induced` or `p.induced`. A mixed pair agrees with `q` unless its outside vertex is in the old second interval. That remaining pair is neither adjacent by separation nor consecutive by interval ordering. If the earlier index is outside the first interval and the later index lies inside it, the earlier index cannot lie in the second interval; agreement with `q` completes that case.

## Consequence for a simultaneous escape

Under first-to-second separation, the constructed intermediate permits the sequential order “replace the first block, then replace the second block.” The second step retains every outside index and has final induced path `q` by hypothesis. Applying the same constructor with `p` and `q` exchanged gives the other-order intermediate under separation of the old first block from the new second block. Outside the two intervals, its vertices still agree with `p`.

Therefore, if both individual blocks belong to a move family already proved closed, a simultaneous replacement that leaves that family must fail cross-separation in both directions. In an undirected graph this means a new vertex from each block must collide with or be adjacent to an old vertex from the other block. This is a written application of the new geometric constructor and the accepted finite-chain principle, subject to the move-family closure premise and the individual block-length restrictions. The source does not assert the native bank closure or a new global bound.

The numerical interval anchors, concrete cube contacts, full move-family enumeration and any successful replacement remain separate obligations. One constructor axiom report is requested. No Lean acceptance claim is made at this preparation stage.
