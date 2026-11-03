# Preserved clause-semantics audit

Status: `PASS_BOUNDED_PRESERVED146_CORE_MAPPING_AND_CYCLE_INTERFACE_AUDIT`.

No mismatch was found between the preserved original input, milestone145 core identities and milestone146 semantic data. The existing generic acyclicity interface suffices for all six retained eight-cycle exclusions. This is a source and data audit, with no new Lean check or actual-snake share theorem.

## Exact input and mapping

The input is the direction sequence `012301`, with five bounds `[0,21]`, share resolution 12, cap 15 and radius 4. Reconstruction produced the exact 11,378-variable, 92,656-clause original input, including its sixteen fixed additional eight-cycle exclusions.

All 12,977 original core IDs agree between `145/work/conversion-long/core-ids.json` and `146/data/share146.json`. Every selected clause agrees with the original input in literal order. The compact core uses clause IDs 1–12,977. Inverse renaming recovers every original signed literal.

The supplied complete-proof variable list has 4,219 distinct entries, all already present among the 5,323 core variables. Every listed proof variable is mapped injectively into the active prefix; their new IDs range from 5 to 5,318. The complete semantic renaming has 5,956 entries: 5,323 active variables followed by 633 additional variables required by the counter and totalizer meanings. Its order is exactly the generated active-first order, and it is a bijection onto 1–5,956.

The audit decoded both packed meaning streams for all 5,957 indices, including dummy index 0, and compared each result with the reconstructed encoder meaning. It also checked all 102 raw-clause chunks, every corresponding tag, the single endpoint-counter table and all 71 share-totalizer tables. The chunks contain 128 clauses each, except the final chunk, which contains 49.

## Retained eight-cycle clauses

All six clauses are tagged `old/cut` and occur in `Share146/Shard101.lean`, under the designated theorem `Snake9.LocalWindow.ShareWindow146.shard101`.

| Original clause ID | Original added-cut index, zero-based | Compact core ID | Shard | Offset, zero-based |
|---:|---:|---:|---:|---:|
|92641|0|12972|101|43|
|92642|1|12973|101|44|
|92643|2|12974|101|45|
|92645|4|12975|101|46|
|92648|7|12976|101|47|
|92652|11|12977|101|48|

Their renamed negative literals decode to precisely the original eight cube vertices. Each set is nonempty, has distinct vertices, is connected, and has exactly two internal cube neighbours at every vertex. Thus each is an induced eight-cycle. The receipt records the vertices, original literals, renamed literals and encoded literals individually.

The other retained cycle clauses were checked against the same degree condition as well. There are 259 retained `old/cut` clauses in total: 208 four-cycle clauses, 45 six-cycle clauses and the six eight-cycle clauses above. The number 259 must not be described as the number of additional eight-cycle exclusions.

## Why the existing interface suffices

`LocalWindowModel.Axioms.acyclic` states that every nonempty list of cube vertices whose members each have at least two neighbours inside the listed set contains an unselected vertex. Its quantifier is unrestricted by cycle length. Distinctness and connectedness are not required by that interface, although both hold for the six concrete sets.

`Tags.ckCut` checks precisely the needed conditions: a nonempty clause, negative primary-vertex literals, and the internal-degree condition on the decoded vertices. `Tags.sound_cut` applies `Axioms.acyclic` directly to that decoded list and obtains truth of the exclusion clause. The share checker reaches this result through the `TagS.old` case of `sound_clauseS`, using `AxiomsS.toAxioms` and the consistency check for old literals. No extra eight-cycle axiom or new geometric hypothesis is necessary.

The inspected `LocalWindowTags.lean` and `LocalWindowModel.lean` copies in `work/final_lean` are byte-identical to the preserved share-model upstream copies. The existing `frame_axioms` source also contains the generic acyclicity argument for normalized snake windows. Its complete instantiation and the final share conclusion are separate from this audit.

## Evidence boundary and remaining work

The milestone145 direct-replay receipt records a complete RUP replay of 285,541 deductions and 31,017,505 hints, ending in the empty clause with the original clause identities preserved. The milestone146 extractor scans the clause portion of every line of that exact pinned proof to produce `proof-variables.json`. This review checked the extractor, list hash, replay receipt and their common proof pin; it did not reread or replay the 233,402,964-byte LRAT file. Completeness of the variable list therefore relies on that preserved extraction provenance. Every variable in the resulting list was independently checked against the full renaming.

No Lean, solver, optimizer or delegated process was invoked. `Shard101` is the designated concrete check for the six clauses; this review does not claim that a new compilation of it has passed. The preserved 105 generated source hashes were checked. New milestone147 imports and compiler receipts are outside this result.

Remaining obligations are the fresh generic and semantic Lean checks, composition of all semantic shards, complete contradiction replay under a consistent variable and clause-ID transport, and the actual-snake geometry and reversal assembly. A completed Boolean replay or a checked `ckAllS` shard alone is insufficient for the actual-snake share-16 theorem.

The frozen receipt is `audit/preserved146-review.json`, SHA-256 `a9aa416c1867fd9478ed32120042e7d5f964ecb79a0f36b95427fa8cb6da5f8a`. It contains the source hash map, every listed proof-variable mapping, exact cycle-clause locations and the checks and limitations above. All writes from this audit are confined to the milestone147 audit directory.
