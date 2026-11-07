# Round 181: closing vertices and necessary window extension

This is the third and final round of the requested continuation, following rounds 179 and 180. Pause after publication. The maintained project interval remains 191–235 edges, with a complete independent rebuild of the archived contributor upper-bound proof still pending. The upper bound 234 remains conditional; no new longer snake is constructed.

## Actual-path deductions

Let an induced path have vertices (p_0,ldots,p_m).

1. If (j-i>2), a common neighbour of (p_i) and (p_j) cannot belong to the path. If it were (p_k), inducedness would force (|k-i|=|k-j|=1), contradicting the index separation.
2. If (m\ge7), every six-edge segment (p_i,ldots,p_{i+6}) extends at one end. For (i>0), its predecessor supplies the extension. If (i=0), the successor of (p_6) exists.

Both deductions pass Lean against the actual `Snake` definition. `ClosingVertex181.lean` also checks the canonical common-neighbour calculation and its application. The two modules have four accepted theorem dependency reports; their ordinary Lean logical axioms are recorded in `data/*-audit.json`. No new axiom or unproved assumption was introduced into these statements.

For the canonical 012301 segment (0,1,3,7,15,14,12), vertices 4 and 8 are the endpoint-common-neighbours. Both are absent from every actual snake containing this segment. For a snake of at least seven edges, a neighbour of 0 other than 1, or a neighbour of 12 other than 14, must also be selected. These are necessary conditions for every length relevant to the upper-bound argument. Translation and coordinate-permutation transfer to arbitrary windows remains part of the geometric interpretation to complete.

## Countermodels identify the missing conditions

| Local input | Result | Integer share | Rational share | Window-neighbour loss |
| --- | --- | ---: | ---: | ---: |
| Original cap-13 input from round 180 | Checked satisfying assignment | 0 | 0 | 0 |
| Original input plus exclusion of 4 and 8 | Checked satisfying assignment | 6 | (52/7) | 5 |
| Previous input plus necessary extension | Native UNSAT; replay pending | — | — | — |

The original model has 223 selected vertices, sixteen eight-cycle components and total loss 5922. The closing-only model has 127 selected vertices, fifteen eight-cycle components and total loss 64517. In the latter, the entire seven-vertex window is an isolated path component. Both assignments satisfy every clause of their saved inputs, and independent enumeration of all 4608 coordinate squares reproduces the physical shares and losses. Neither is an actual snake or a counterexample under the global loss-at-most-one hypothesis.

The original model establishes a specific limitation: a remainder budget over neighbours of the window alone does not imply the proposed share floor in this relaxation. Closing exclusions remove that model, but an isolated window still survives. Necessary extension excludes this second obstruction.

The extended input has 10,854 variables and 89,490 clauses. It differs from the original saved input only by two negative units and one extension clause. The native solver returned UNSAT in approximately 61.28 seconds, with a 94,066,751-byte uncompressed proof. `data/extended14.json` pins the inputs, producer, solver output and compressed evidence. Complete replay was attempted twice, but both attempts stopped before reading the proof because available memory was below the fixed 1 GiB startup requirement. The exact failure records are preserved. This remains a native refutation awaiting replay, and is not a completed Lean local-share theorem.

## Completed native proof replay

All three round-180 UNSAT certificates pass full native ordered-RUP replay, including the final empty clause. The checker verifies the original CNF and proof hashes, honors deletions and checks every added clause against its propagation hints. No proof trimming is used.

| Pattern | Checked added clauses | Propagation hints |
| --- | ---: | ---: |
| 012034 | 99,002 | 3,558,610 |
| 012340 | 86,067 | 3,400,513 |
| 012345 | 254,332 | 15,443,442 |
| Total | 439,401 | 22,402,565 |

These are native certificate checks, separate from Lean contradiction checking and the arbitrary-snake interpretation of each Boolean input. The new certificates also do not complete the older share-18 Lean replay, which remains at 33,111 of 145,215 deductions without its final contradiction.

## Remaining mathematical requirements

Under the retained local and graph premises, the uniform floor-14 potential gives

\[
42248m+45L\le9928364.
\]

Thus (L\ge2) gives (m\le234); any remaining hypothetical snake with (m\ge235) has (m=235) and (L\in\{0,1\}). All four floor-14 proofs and their geometric interpretation still need their complete Lean chain. Retained count restrictions, reference exclusions and graph coverage remain unresolved as documented in the current handoff.

Round 179 showed that, on the four pending patterns, the rational-to-integer window deficit is at most (2/5) when (L=1). A strict rational-share bound greater than (72/5) would therefore imply floor 15 in both remaining loss cases. Equality at (72/5) is insufficient for this deduction. No such rational lower bound is proved here. The original cycle model shows why a purely local remainder restriction requires additional path information.

On resumption, first replay the saved extended 012301 proof without rerunning the solver. Then complete the Lean and geometric certificate chains. Further local strengthening should retain the closing and extension conditions and distinguish global loss from a window's remainder sum.

## Saved evidence and resource limits

- `lean/`: the two actual-snake proof modules.
- `data/`: accepted proof receipts, native replay records, reconstructed models, solver records, startup stops and completion status.
- `certificates/`: compressed original local inputs and solver proof outputs for the closing and extended queries. The closing query is SAT; its partial solver proof output is not a refutation.
- `scripts/`: the exact producers, native proof checker, model reconstruction, document update and scoped publication helper.
- `source-before/`: the pre-update manuscript and short explanation, preserving the previous text.
- `logs/` and `build/`: compiler and solver evidence. Large uncompressed inputs and proof caches remain local in `cache/`.

The streamed solver used a 1 GiB startup requirement, 256 MiB combined private-memory limit, 768 MiB free reserve, 90-second time limit and 128 MiB raw-proof limit. Native replay used the same startup/private/reserve guards and a 240-second limit. An earlier full-encoder attempt at floor 15 did not start under its existing 1.5 GiB startup requirement. The first extended-query startup also stopped; a later attempt completed under the unchanged guard. No resource failure establishes a mathematical exclusion.

The manuscript and short explanation are updated in place, with author order and hyperlink settings preserved. Publication includes the exact-byte manifest. Research stops after this round; a new user instruction is required to resume.
