# Round 180: floor14 certificate searches and a zero-share cycle obstruction

Second of the three requested rounds. All four radius-four, count-free queries used the existing TaggedShare encoding, bounds0–21 at each of five centres, and share cap13. No additional cycle cuts were inserted. The base encoding already excludes selected squares and its specified six-cycle configurations.

| Pattern | Native outcome | Solver seconds | Raw LRAT bytes |
| --- | --- | ---: | ---: |
| 012034 | UNSAT, replay pending | 22.44 | 30302424 |
| 012301 | SAT, full assignment checked | 0.31 | 325021 |
| 012340 | UNSAT, replay pending | 21.78 | 28078670 |
| 012345 | UNSAT, replay pending | 85.80 | 122182401 |

The three UNSAT outputs are native proof-search results, not completed Lean local theorems. Compressed original CNFs, semantic tables and complete LRAT outputs are saved. Solver time was capped at90 seconds, private memory at512MiB including the parent, with768MiB free-memory reserve and a128MiB raw-proof cap. No failed or incomplete search is promoted to an impossibility claim.

The012301 assignment was independently checked against every original CNF clause and decoded into selected cube vertices. Direct enumeration of all4608 coordinate squares gives five actual shares[0,0,0,0,0]. The selected set has223 vertices and sixteen induced eight-cycle components, as well as other components. Its total loss is5922, while the loss over all neighbours of the five window centres is zero. Consequently a local remainder budget at most one would not eliminate this assignment. It is not a snake and does not refute the desired universal share floor for snakes.

The canonical012301 window is0,1,3,7,15,14,12. Vertices4 and8 are the two common neighbours of its endpoints. Either, if selected, completes the window into an eight-cycle. The saved assignment selects8. Every actual induced path containing this six-edge segment must exclude both closing vertices. This is a written path argument to be checked and used in round181. It directly addresses the observed local obstruction, rather than treating small local rounding loss as sufficient to establish the missing share floor.

Read data/012301-model.json for the exact assignment, component decomposition, shares and loss, and data/results.json for all solver records. Large uncompressed proof/cache files remain local; publication includes their compressed counterparts. The original tagged encoder and solver hashes are pinned. The inherited graph/count assumptions and all global bound qualifications are unchanged.

One requested round remains. Round181 will apply and justify the closing-vertex exclusions, inspect their effect on the012301 query, and verify the available native proof evidence where resources permit. Pause after that round.
