# Round 225 final bounded document review

Conclusion: no unresolved mathematical or evidence-scope error was found in the final revised passages. The two corrections identified during review have been applied: the main manuscript date now states round 225, and the short explanation explicitly requires each replacement interior to be disjoint and nonadjacent to retained vertices outside its own closed interval. The reported exclusion is restricted to the selected seed, unchanged outside indices, equal-length two-block replacements, appended endpoint 24, and four coordinate-8 crossings. It establishes no new global bound or longer snake.

## Frozen document identities

| Artifact | SHA256 |
|---|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | `c55a8715e8286b544d52bfdcd7b1574ada75acc6dbefde7010bb317eec5965a1` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | `09e3df2e5006d2fe792abd1553205ed2349935ed67f45ee70497f2d97a61300d` |
| `MATHEMATICAL_NOTE.md` | `ce5c69bb08a0f58458be2d605dea257e94ae35d926e6068df779e4bfcd6d330e` |
| `data/snake9_research.tex.before.txt` | `45aab4f0f416f4ca32fbd58f210aa21f1282bdb39d7ed1698f5aad433fc490e8` |
| `data/snake9_frontier_explanation.tex.before.txt` | `c378fefa4c13730c27d1001422e15dd8a21949bf96e7c02380c639966eeb1dca` |

Both editor originals are byte-for-byte identical to their respective `E:/Snake-in-a-box/paper/` mirrors. The final main source has 11,622 lines; the short explanation has 538 lines; the mathematical note has 50 lines.

## Read scope and preservation

Read the complete round-225 unified diffs of both manuscripts against the saved before files, including the final corrections. Read the entire short explanation, lines 1–538; main lines 1–99, including the complete abstract, and lines 7897–8155, including the complete new replacement subsection and verification section; and the entire mathematical note, lines 1–50. The added bibliography entry was read in the complete diff. This is a bounded revision review, not a rereading of the entire main manuscript. The full-paper review remains scheduled for round 230.

All three author names, their existing author commands, and the main `hypersetup` metadata are unchanged. The short source had no `hypersetup` block and still has none. Every previous label and bibliography key is retained. Main labels increase from 355 to 357, adding only `sec:replacement225` and `prop:simultaneous225`; bibliography keys increase from 122 to 123, adding only `research225`. The short source remains without labels and adds only `research225`, increasing its bibliography from seven to eight entries.

## Mathematical statements

The main simultaneous-replacement proposition has sufficient local hypotheses. Pairs within a closed replacement interval are handled by the local path; retained pairs inherit the original path relation; all remaining pairs satisfy the separation conditions. Retained anchors ensure that separated pairs cannot be consecutive. Shared anchors and empty interiors cause no gap. The final short explanation now states the necessary retained-vertex nonadjacency explicitly.

Interval enlargement preserves the same complete candidate and outside agreement. The numerical transfer uses only excluded containing width-44 contexts. It does not interpret an unresolved containing context as evidence of exclusion. The manuscript preserves the distinction between this generic implication and the source-native exclusions.

The coordinate-crossing relation follows from successive bit flips: the count has the parity of the endpoint disagreement. For width 42, the seven remaining contexts have first interval [1,43], second interval [c,c+42] for 124 <= c <= 130, equal endpoint bits in each block, and total replacement crossing count two. Thus the allocations (0,2) and (2,0) exhaust the possibilities. The maximal-window enumeration and fixed-family qualification agree with the earlier model and split reviews.

The unchanged global interval 191 <= a(9) <= 233, the pending independent rebuild of the contributor chain, and the fixed-parent one-crossing ceiling are kept separate from the new local exclusion. The short explanation retains the explicit absence of an attained compatible 92-edge partner. Opening contributor revision `9698e87a` and closing revision `d6512400` agree with `data/github-review.json` and are described only as work in progress toward 231.

## Native counts and incomplete continuations

Read `data/search-summary.json`; independently counted the saved records in every `pair34.json` through `pair43.json`; checked complete context IDs, terminal exit-zero execution receipts, and current source/script hashes. The manuscript table agrees in every column:

| Width | Contexts | Inherited | Geometric | Newly excluded | Unresolved |
|---|---:|---:|---:|---:|---:|
| 34 | 231 | 197 | 12 | 22 | 0 |
| 35 | 238 | 199 | 15 | 24 | 0 |
| 36 | 245 | 201 | 13 | 31 | 0 |
| 37 | 252 | 203 | 8 | 41 | 0 |
| 38 | 259 | 205 | 0 | 54 | 0 |
| 39 | 266 | 207 | 0 | 59 | 0 |
| 40 | 273 | 209 | 0 | 64 | 0 |
| 41 | 280 | 210 | 0 | 70 | 0 |
| 42 | 287 | 211 | 0 | 76 | 0 |
| 43 | 294 | 211 | 0 | 58 | 25 |

The initial width-42 result correctly retains 69 infeasible and seven unknown native queries. Each split result contains exactly IDs 63–69, all infeasible, under the specified first crossing count zero or two. `combined42.json` has 211 inherited, 69 initial infeasible and seven split-excluded contexts, with no unresolved record; all its saved file pins match. Therefore the final 76 counts contexts, rather than treating the fourteen split queries as fourteen additional contexts. Width 43 remains at 25 unresolved contexts.

The original direct result and checkpoint agree on 30 seconds, 1,979,706 processed first prefixes, 15,013 complete first paths, 15,013 second-root examinations, and 25 pending first prefixes. The second-root failure interpretation is supported by the source and context geometry: its anchors are 357 and 473, distance five, both in the upper face, with a two-crossing budget; neither anchor can be removed by the first prepared domain. The remaining root rejection checks are connected-component and size/colour capacity checks. No successful second path or exhaustion is recorded.

The separate pruned result and checkpoint agree on 30 seconds, 794,271 processed first prefixes, zero complete first paths, and 20 pending first prefixes. Its second-domain rejection counts sum exactly to 249,163: 173,720 disconnected, 44,686 insufficient size and 30,757 insufficient colour capacity; anchor-removal count is zero. Both results say `TIME_LIMIT`, `exclusion: false`, and `whole_context_excluded: false`, with allocation (0,2). Both saved checkpoint hashes match. The documents correctly retain incompleteness and make no measured full-search speedup claim.

The original result SHA256 is `077fbaa73e5a7f54f76d8a70a8a7a8f9acd89c1300a6bed64ea26316110cbfeb`; its checkpoint SHA256 is `3505cc1bda640fa6d16db2f7ec1d260229b35637090ead5360ed57917caadf3c`. The pruned result SHA256 is `7b89146b9f3402d687e5dd004b5db3aab2a3e352c4e239cadb4746fba59f0820`; its checkpoint SHA256 is `6777944b1c9562355c9e09a4ca258bf0da33900007b93619037c5e716c0aa1ba`.

## Lean and compilation evidence

Inspected the final constructor statements and local-premise packaging, together with the independent interval-enlargement and endpoint-parity statements. The constructor takes local distinctness, local inducedness, outside agreement and separation premises; it does not assume global candidate inducedness as a field.

All eight entries of `data/accepted-proof-summary.json` agree with their accepted audit records: `ReplacementIndices225`, `ReplacementCases225`, `ReplacementPairs225`, `ReplacementConditions225`, `ReplacementOrdered225`, `Simultaneous225`, `IntervalEnlargement225`, and `EndpointParity225`. Each has `PASS` and compiler exit zero. Recomputed hashes of every accepted record's source, compiler log, output object and listed dependencies match. Read the corresponding compiler reports: their 18 printed declarations use no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`; several declarations report no axioms. No failed or interrupted attempt is counted as acceptance.

These receipts support the generic constructor, outside-agreement and parity claims. They do not certify the finite native model enumeration, solver contradictions, concrete domain arrays or connected-search traversal. The final documents state that limitation.

Read `data/main-compile-final.json` and `data/frontier-compile-final.json`; both report successful compilation of the editor originals. These are the parent's saved compilation receipts. This reviewer did not invoke a compiler or inspect rendered PDF pages.

## Remaining handoff condition and limits

At the review freeze, `data/completion.json` had not yet been generated. The mathematical note references that finalizer output for accepted receipts and continuation hashes. The final publication must include the generated manifest; its contents are outside this pre-finalizer review. The underlying receipts and checkpoints were inspected directly above.

No manuscript, native result or previous review was edited by this review. No optimizer, compiler or software test was run. The evidence work comprised source reading, exact count aggregation and file-hash comparison. Earlier domain, split and connected-search reviews remain separate and unchanged. No complete native contradiction replay or independent rebuild of the archived upper-bound chain is claimed.
