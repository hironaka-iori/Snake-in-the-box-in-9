# Active route · One crossing between two eight-dimensional arms

**Continue this route across successive rounds.** Seek a 192-edge snake in the ninth-dimensional cube by placing one induced path in each eight-dimensional face and joining their endpoints across one edge. Fix a long parent and search over the entire other face. Keep the first arm, endpoint orientation, case coverage and strongest checked result identifiable at every pause.

## Why these three length splits suffice

Translate the two joining endpoints to zero in their respective faces. The joined path is induced exactly when the projected arms share only zero. A join with arms of lengths $a,b$ has $a+b+1$ edges. Since each arm has at most 98 edges, any one-crossing path of length at least 192 can be shortened at its free ends to 192 while retaining the crossing. Its unordered arm lengths are then $(96,95)$, $(97,94)$ or $(98,93)$.

## Where to resume after Round 249

**Round 250 starts with donor 16, position 72 (record `16:72`).** Its 96-edge path has endpoints 1 and 70 in the saved labelling. At position 72, vertex 16 replaces vertex 82, between neighbours 18 and 80. The old parent excludes a 94-edge partner from either end. Any 95-edge partner of the changed parent must therefore visit 82 within its first 94 edges. It visits 82 internally, because the joining endpoint and 82 have the same parity. Search both endpoints; in root-normalized coordinates the required vertex is 83 or 20 respectively. [New sequences and their hashes](../../milestones/249-long-parent-joins/geometry.json)

Continue through the seven new shapes on this same route. The five 96-edge shapes are `16:72`, `17:71`, `99:85`, `114:85` and `901:72`. They need 95-edge partners. The two 97-edge shapes, `19:72` and `902:72`, need 94-edge partners. These seven represent all new shapes reachable from the original fifteen by any number of legal single interior-vertex changes with endpoints fixed. Larger replacements, endpoint changes and independently generated parents remain within the route if those seven close. Record all remaining branches at each pause.

The first fifteen recorded parents (eleven of length 96, three of length 97 and one of length 98) have been excluded for a 192-edge join with an unrestricted partner. A larger family of eight-dimensional parents remains open. The full manuscript review is due in Round 250. [Round 249 and certificate inventory](../../milestones/249-long-parent-joins/README.md) · [Earlier classification of 191-edge joins](../../milestones/248-rooted-arm-capacity/README.md) · [Reusable goal](RESEARCH_GOAL.md)

The [lower-dimensional examples](../../milestones/188-dimensional-constructions/MATHEMATICAL_NOTE.md) illustrate why the crossing count matters. They give explicit compatible pieces for lifts, including a 50-edge path built from three six-dimensional pieces. They supply examples for constructing new parents without imposing a recurrence on the maxima.
