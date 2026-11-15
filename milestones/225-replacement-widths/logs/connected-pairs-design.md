# Direct connected replacement search

Prepared source: `scripts/connected_pairs.py`. It has not been executed, compiled or tested. No performance or exclusion claim is made.

The command accepts `--width`, `--id`, `--tag`, `--seconds`, and optionally `--resume PATH`, `--first-part 0|1`, and `--first-crossings N`. The selected `data/regionsW.json` row must contain two prepared domains and have preparation status `PENDING`. A later native result may already have resolved that row; choosing a currently open row remains the caller's responsibility. Results and checkpoints are written separately to the fresh directory `data/TAG/result.json` and `data/TAG/checkpoint.json`. Existing tag directories are rejected. Resumption requires matching input, script, part order and allocation hashes/values and uses a new output tag.

`--first-part` changes enumeration order only. `--first-crossings` restricts the first-enumerated part to that crossing count and fixes the other count by subtraction from the combined budget. In a context with same-face anchors and combined budget two, the only allocations are $(0,2)$ and $(2,0)$. Running `--first-part 0 --first-crossings 0` covers the first allocation; `--first-part 1 --first-crossings 0` covers the second, beginning with the zero-crossing block in each case. Both must be exhausted before combining them into a context exclusion. This split is valid only after checking those particular anchors and budget. The script itself supports unrestricted allocation enumeration by omitting `--first-crossings`.

## Enumerated family

The first search enumerates actual induced paths from the first original anchor to the second, using exactly the selected width in edges. For each complete first path, the second domain loses every vertex equal or adjacent to a first-path vertex. The second search then enumerates actual induced paths of the same prescribed length between its anchors. The two index intervals are separated, so the final path permits no adjacency between their selected vertices. No mutual contact with old omitted interiors is required.

Prepared domains remain premises of this implementation. Their necessary-condition construction and source identity are inherited from `regionsW.json`; its dependency hashes are checked. The two crossing counts must sum to the saved replacement budget, independently recomputed as four minus the crossings in the unchanged portions of the seed. Individual crossing parity agrees with the coordinate-8 difference of that path's endpoints.

## Necessary pruning conditions

1. If a prefix leaves $r$ edges, Hamming distance to its target must be at most $r$ and have the same parity. Reaching the target early is forbidden.
2. A prospective vertex is removed if it repeats an earlier prefix vertex or touches an earlier vertex other than the current endpoint. The final anchor cannot touch an earlier nonconsecutive prefix vertex. If the current endpoint touches the final anchor, exactly one edge must remain; otherwise that adjacency would be a chord.
3. After removing forbidden vertices, the component of the current endpoint must contain the target and at least $r+1$ vertices. Its even and odd vertex counts must accommodate an alternating path of $r$ edges beginning at the current endpoint. The component is an overestimate of the possible remaining path, so these shortages justify rejection.
4. Coordinate-8 crossings already used are counted exactly. For the first prefix, the remaining first-path crossings and all second-path crossings must admit nonnegative counts within their remaining lengths, with the appropriate endpoint parities and the prescribed total. During the second search, its remaining crossing count is fixed by the first complete path. No additional upper bound on crossings is presumed.

Every admissible next neighbor is retained in the DFS frontier. Ordering by vertex number affects traversal order only. These conditions are necessary; they do not assert that a surviving prefix can be completed.

## Checkpoint and conclusion scope

The checkpoint stores both DFS prefix stacks and the active phase. While the second stack is explored, its associated complete first path remains at the top of the first stack. It is removed only after the second stack is exhausted. Frontier replacement uses a single state assignment after computing an expansion, so interruption during expansion leaves its original prefix pending. A checkpoint taken during an interrupted counter update may overcount processed work; its search coverage is preserved.

The wall-clock limit is checked between complete prefix operations. A component traversal visits at most 512 cube vertices. Checkpoint writes and the final independent witness audit can extend wall-clock time beyond the requested search budget. A periodic checkpoint is written at most once per five seconds. `KeyboardInterrupt` saves the current frontier. A forced process termination may lose work since the preceding checkpoint, whose pending prefixes remain available for conservative repetition.

Only an empty first frontier after completion of all associated second searches produces `EXHAUSTED` and `exclusion: true`. With a fixed crossing allocation this excludes only that allocation; `whole_context_excluded` remains false and `exhaustion_scope` states the restriction. An unrestricted exhausted search sets `whole_context_excluded` true. `TIME_LIMIT`, `INTERRUPTED` and `ERROR` do not assert exclusion. A found candidate is accepted only after reconstructing all 193 vertices in original interval order, checking distinctness and every pair's adjacency against consecutive path positions, confirming endpoints 0 and 24, recounting all four coordinate-8 crossings, and checking any selected allocation. That produces `WITNESS`.

This is native enumeration of one specified replacement context. It has no Lean traversal certificate and cannot yield an unrestricted upper bound. Checkpoint provenance guards source consistency; they are not an independent proof that a checkpoint's frontier is complete.
