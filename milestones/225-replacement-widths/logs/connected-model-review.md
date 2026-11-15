# Connected replacement search review

15 November 2026. No invalid pruning or branch-coverage error was found in the two reviewed DFS sources. One terminal-interruption resume limitation and one historical wording issue are recorded below. Neither creates a false exclusion.

Read every line of `connected_pairs.py` (302 lines), `connected_pruned.py` (344 lines), and both design notes (32 and 15 lines respectively). This is source and mathematical review only: no program, optimizer, compiler or software tests were executed. No saved frontier was independently replayed and no runtime improvement, witness or exhaustion result is asserted here. Only this log was written.

## Enumeration and pruning

Each prefix starts at the prescribed anchor. An expansion considers every cube neighbour of its last vertex that remains in the allowed domain, is unused, and is nonadjacent to all earlier nonconsecutive prefix vertices. The target is allowed only on the final edge. This produces exactly the possible next steps of an induced replacement; numeric ordering changes traversal order only.

The Hamming-distance lower bound and parity check are necessary. An early target visit cannot be extended into a simple path ending at that target. Adjacency between the target and an earlier prefix vertex would be a chord; adjacency to the current vertex requires exactly one remaining edge. Removing earlier vertices and their neighbours leaves an overestimate of the possible continuation domain. Its current-vertex component must contain the target and enough vertices of both alternating parities. These tests therefore cannot remove a valid completion.

Crossing pruning accounts for the crossings already used, remaining first-path length, remaining endpoint-face parity, and a nonnegative second-path crossing count of the required parity. With a fixed first allocation it also enforces that allocation. During the second search, the first complete path fixes the residual budget. These are necessary conditions; the first-stage existence check may retain impossible prefixes but does not exclude a valid pair.

For every complete first path, the second domain removes all vertices equal or adjacent to any first-path vertex. This is required because the replacement intervals are separated and have no intended cross-part adjacency. The second DFS then enumerates every compatible induced path between its anchors. Neither source imposes a contact requirement with old omitted interiors.

The additional pruning in `connected_pruned.py` is valid. Every extension of a first prefix can only remove more vertices from the second domain. Removed second anchors, disconnected anchors, insufficient component size or insufficient parity capacity cannot be repaired by extending that prefix. The zero-crossing first-domain face restriction is applied only when `--first-crossings 0` is explicit; a zero-crossing path necessarily stays in its starting face.

## Frontier and checkpoint coverage

Replacing one pending prefix by all of its children preserves the unexplored family. Expansion and pruning are computed before a single assignment replaces the state. An interruption before that assignment leaves the old prefix pending; an interruption after it leaves all surviving child prefixes pending. Counter increments can precede state updates, so interrupted/resumed counts need not count distinct processed states exactly.

Crucially, a completed first path remains at the top of `first_frontier` throughout its second DFS. It is removed only when `second_frontier` is empty. The second domain is recomputed from that pending first path after resumption; the cache is not required for completeness. This avoids the loss of first-path cases while their second searches remain unfinished.

Each checkpoint write uses a temporary file followed by replacement. A forced termination may discard progress since the preceding complete checkpoint, whose larger pending region remains available for conservative repetition. The checkpoint and result are separate writes; interruption between them can leave a result referring to an earlier checkpoint hash. Consumers should verify that link and use the intact checkpoint for resumption. Script, source, interval order and allocation pins must match. The new pruned worker deliberately rejects original-worker checkpoints rather than silently transferring them.

These arguments establish the source's frontier invariant for its own generated states. Structural resume validation and matching hashes do not independently prove that an arbitrary supplied checkpoint contains the entire unexplored region.

## Witness and conclusion scope

The route array is restored to original interval order even when enumeration starts with part 1. The final audit reconstructs all 193 vertices, checks distinctness and every unordered adjacency pair, confirms endpoints 0 and 24, checks the four total bit-8 crossings and verifies any fixed crossing allocation. A failed audit produces an error, never an exclusion.

`--first-crossings` refers to the **first-enumerated** interval. With `--first-part 1`, zero crossings therefore means original allocation $(2,0)$ when the total is two. This differs from the CP split source's fixed original-first-part convention. The saved allocation is in original part order and the witness audit uses that order correctly.

`EXHAUSTED` is reached only after the first frontier is emptied, including all associated second searches. With an explicit allocation it excludes only that allocation and leaves `whole_context_excluded` false. Omitting the allocation permits a whole prepared-context exhaustion claim. `TIME_LIMIT`, `INTERRUPTED` and `ERROR` do not exclude anything. A single selected width-43 context/allocation does not resolve the full width-43 family. These remain native enumerations without a Lean traversal certificate.

## Minor limitations

1. An interrupt can occur after the last first-frontier entry is removed but before the loop assigns `EXHAUSTED`. The handler then saves `INTERRUPTED` with an empty `first_frontier`; resumption rejects that record because its guard requires a nonempty first frontier. No unexplored branch is lost, but this terminal interruption needs explicit handling before automatic continuation. This is a static code observation, not an observed failure in the current runs. No live source change was made.
2. The original design note says the worker “has not been executed”. That sentence describes preparation-time status and should be labelled accordingly now that run records exist. The pruned design note already uses the qualified wording “during preparation”.

## Reviewed hashes

| Artifact | SHA256 |
|---|---|
| `scripts/connected_pairs.py` | `7c1c1dc41c4b7c73ef0038b417f9a09d7068c5b474217ccf272ad2c4b4e4c74a` |
| `scripts/connected_pruned.py` | `609726b4d5679e0f1fbb287af7f025b3c5d1508aa5f195be3510964e3f58db80` |
| `logs/connected-pairs-design.md` | `9aba278b964bbce88558588933b75cc0c9668924e19da26c829400e5718ff44b` |
| `logs/connected-pruned-design.md` | `c4eb99b72829669ce10da2e74aca51aa873b016d30835eab7bdd1e568e38019d` |
