# Round 225: simultaneous replacement criteria and crossing allocation

The endpoint-24 construction from the selected 191-edge Q9 seed is computationally excluded when both replacement blocks have at most 42 edges. At width43, 25 of294 maximal contexts remain unresolved. No192-edge snake or new global bound is obtained. The goal remains active and concerns constructions; coworkers handle upper bounds.

## Exact family

Use the normalized bank123 seed recorded in milestone223. Its endpoints are0 and88; its four coordinate8 crossings are at edge indices46,130,163,177. Appending24 requires removing original vertices28 and56 at positions7 and143. Change two open index intervals, retaining their anchors, every outside position and equal path lengths, then append24. The final path must have193 distinct vertices and exactlyfour coordinate8 crossings. No mutual-contact filter or bank-closure premise is used.

For width w, maximal intervals are[a,a+w] with0<=a<=6 and[c,c+w] with144-w<=c<=142. Their7(w-1) contexts cover any shorter pair containing the two blockers: enlarge each interval with unchanged seed positions. Other seeds, endpoints, more regions and length-changing replacements are outside this exclusion.

## Mathematical arguments

Two local replacement paths assemble into an induced path if each is induced on its closed interval, each new interior avoids equality and adjacency with retained vertices outside that interval, and the new interiors avoid each other. Every pair lies in a local interval, is retained, or satisfies one of these separation conditions. Retained anchors ensure the separated pairs are nonconsecutive. This constructs the final path without assuming its inducedness or either intermediate path's validity. Shared anchors and empty interiors are permitted.

Outside agreement survives interval enlargement. Therefore a smaller candidate would also belong to any containing larger context with the same full-path conditions. Only STATIC_EXCLUDED and INFEASIBLE width44 parents are used; UNKNOWN is never exclusion evidence. The independent containment enumeration covers2053 of2625 width34–43 contexts. The transferred numerical result retains its source-native status.

Each coordinate crossing flips its bit. Hence a path's crossing count equals its endpoint disagreement plus twice a nonnegative integer. For the seven initially unresolved width42 cases, both anchor pairs have equal coordinate bits and the combined crossing count is2. Exactly the allocations(0,2) and(2,0) remain. All14 allocation queries are infeasible. The seven cases have first interval[1,43] and second[c,c+42],124<=c<=130. This closes width42 completely.

## Native outcome table

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

At width42 the newly excluded column includes seven contexts closed by both allocation queries. Saved initial pair42.json still correctly records seven UNKNOWN outcomes; combined42.json and search-summary.json record the subsequent complete split. The split worker's inherited wording “all maximal contexts” is overbroad: each split run covers only IDs63–69 and its specified first-path crossing count. Its exact arguments, filters, models and the independent review establish the actual restricted scope.

The geometry and model sources have independent reviews. Every native exclusion remains without a Lean contradiction certificate. All per-query input models are retained locally; solver-models.zip publishes their exact bytes. Dynamic cycle cuts, if any, are recorded separately in the query results. COMPLETE_COVERAGE means all requested contexts were visited; it alone does not establish exclusion.

## Connected-path continuation

The first direct search uses width43 context22, intervals[0,43] and[123,166], allocation(0,2). In30seconds it processed1,979,706 first-path prefixes and15013 complete first paths. Every associated second search failed at its root. No witness was found;25 first-prefix branches remain. The checkpoint retains them, and no exhaustion is claimed. This motivates pruning a first prefix when its closed neighbourhood already leaves too little connected space for the second path. The second path must avoid every already selected first vertex and neighbour, so this is a necessary-condition pruning rule.

The original DFS source/checkpoint remain frozen. A changed search must not overwrite or silently resume that checkpoint under changed source pins. The separate pruned43-22-zero run processed794,271 first prefixes in30seconds, pruning249,163 prefixes because the second graph was disconnected or had insufficient size or colour counts. It found no complete first path and remains TIME_LIMIT. This is a stronger necessary-condition search, without a measured full-search speedup or an exhaustion claim. Both preparation design notes record their status at the time they were written; subsequent execution receipts supersede that preparation-only status. The latest checkpoints and result hashes are in completion.json.

## Logic status and next step

The final accepted proof receipts, including the direct constructor, interval enlargement and endpoint parity, are listed in completion.json. Compiler memory interruptions are preserved in logs; an interruption is not acceptance. Generic Lean implications and finite native exclusions have different scopes.

Continue actual connected-path enumeration in the25 open width43 contexts, prioritizing the two possible crossing allocations and early capacity of the compatible second graph. Preserve incomplete frontiers. A successful193-vertex candidate must pass the complete all-pairs induced-path audit before it is reported as a192-edge lower bound. Local exclusion through42 does not predict the global optimum and does not establish196.

The maintained project interval remains191<=a(9)<=233; the independently rebuilt233 contributor chain is still pending. The opening contributor snapshot9698e87a and closing snapshotd6512400 record work in progress toward231, with no new completed bound imported this round. Frozen parent-history cases22/23/24/9 and the completed fixed-parent one-crossing result remain unchanged.
