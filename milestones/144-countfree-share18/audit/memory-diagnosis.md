# Source diagnosis of the first-check memory stop

Selected design: construct the initial tree directly in preorder, remap the allocated clause keys consistently, and retain the existing RUP checker and soundness chain. This is a proposed implementation; no new Lean code was compiled or executed during this diagnosis.

## Observed facts and limits

The saved stop record reports six successful modules and termination of `LocalWindowUnsat.ShareWindow144.Check1` under severe physical-memory pressure. Its compiler log is empty. There is no per-theorem progress report establishing whether `ok1`, a later theorem in that module, initialization, replay or checkpoint comparison was active at the stop. The evidence does not establish which component dominated memory.

`Data0.lean` defines:

```lean
noncomputable def start1 : Tree := loadRaw (perf 14 0) raw inputSlots
```

The list contains 13,224 distinct input slots. The depth-14 perfect tree has 16,383 nodes. `loadRaw` performs one persistent `insertF` per input clause and explicitly forces intermediate trees through `seqT`. This construction remains unchanged when the replay hint threshold is reduced.

`Check1` checks four consecutive segments with 6,006, 6,018, 6,114 and 6,195 hints, totaling 24,333. Its later starting states are nested `replay` expressions, and the fourth theorem also checks the transition to a checkpoint. Smaller segments or one theorem per module could reduce this replay work, but they do not remove the 13,224 initial insertions. Smaller segments alone therefore have no established sufficiency.

## Recommended initial constructor

Use a new helper with the following recursive behavior, keeping the current `Tree`, `rawMask` and `perf`:

```text
rawPre 0 b raw = (Tree.nil, raw)
rawPre (d+1) b [] = (perf (d+1) b, [])
rawPre (d+1) b (c :: cs):
    (left, remainingLeft) = rawPre d b cs
    (right, remainingRight) = rawPre d (b + 2^d) remainingLeft
    return (Tree.node (b + 2^d) (rawMask c) left right,
            remainingRight)
```

This produces the same ordered perfect-tree shape used by `LratFast144`. It consumes raw clauses directly in preorder and fills the unused suffix with tautologies. It avoids constructing the initial database by repeated insertion. The proposed initial state is `(rawPre 14 0 raw).1`.

The required soundness lemma has a paired conclusion. Assuming every decoded input clause is true under an assignment, depth induction proves both:

1. `TreeTrue` holds for the returned tree.
2. Every decoded clause in the returned remainder is true under the same assignment.

The zero-depth case returns the input unchanged. The empty-input case uses `Snake9.LratFast144.perf_true`. In the nonempty case, split the `List.all` hypothesis into the head and tail, use `Snake9.Lrat144.rawMask_true` for the root clause, apply the induction hypothesis first to the left subtree and then to its remainder for the right subtree, and combine the results with `Snake9.Lrat144.TreeTrue.node`. The remainder invariant supplies exactly the hypothesis needed for the right recursive call. This proof needs no permutation argument, no large membership certificate and no equality with the old `loadRaw` expression.

An optional bookkeeping lemma can identify the remainder as `raw.drop (2^d - 1)`. It is unnecessary for the paired truth invariant. For this input, 13,224 clauses fit within the 16,383-node tree.

## Required key remapping

Let `input_slots[i]` be the existing allocator's physical slot for the compact core clause at position `i`, and let `preorder_keys(14)[i]` be the existing generator's key at preorder position `i`.

- Assign the new key of `input_slots[i]` to `preorder_keys(14)[i]` for all 13,224 input clauses.
- Assign the remaining 890 allocated physical slots injectively to the next unused preorder keys. The other 2,269 tree positions remain available as tautology-only positions outside the allocator's domain.
- Retain the allocator's logical clause lifetimes and physical-slot reuse. Replace its old physical-slot-to-key map everywhere: destination words, hint words, checkpoint entries, final empty-clause key and any input-key metadata.
- Regenerate all packed proof arrays and checkpoints. The old packed proof cannot be combined with the new initial state.

All new keys must be distinct on the allocator's domain, nonzero and at most 16,383. They fit the existing 14-bit format. The variable renaming, offset 8,192, CNF, original clause-ID provenance and semantic modules need not change.

The existing generator hooks are `plan` and `perfect_keys`, followed by the uses of `key` in packed destinations/hints, checkpoint dictionaries and `final_key`. The initial definition is emitted in `Data0.lean`; the final contradiction currently invokes `start_true` and must instead invoke the new paired lemma's first conclusion. The existing `replay_true`, `cp_true` and `final_false` remain applicable because they require a true initial tree rather than its particular construction history.

## Comparison with the other proposed constructions

A literal balanced tree with a direct proof for each occupied clause also avoids insertion. Its soundness can use `rawMask_true`, `maskTrue_taut` and `TreeTrue.node`. However, arbitrary existing key order would require linking each clause to the global raw premise, preferably through the 104 existing chunks. That introduces many membership or extraction proofs. Preorder loading removes this additional proof obligation by consuming the original raw list in order.

Chunked `loadRaw` with static checkpoints is also sound using the existing `loadRaw_true`, `cpOk_true` and `perf_true`. Each chunk would load at most 128 clauses, then prove `cpOk` against its next checkpoint. However, a checkpoint after the entire load does not avoid evaluating the entire load; checkpoints must interrupt the loading sequence. This would introduce up to 104 checks over substantial trees and retain repeated insertions. It has a smaller generic-proof change but a larger checkpoint-verification burden. It is not the selected first approach.

## Acceptance checks before further replay

Preserve the audited export and failed warm-up. Generate the changed constructor, key map, proof arrays and plan in a separate experiment.

First check the small generic paired soundness lemma and its standard axioms. Independently verify that the new key map is injective and that every original core clause appears at its assigned initial key, with tautologies at every other tree position. Rerun the producer's complete packed simulation with the regenerated keys and checkpoints; the old simulation receipt does not cover this transformation. Then check a single first replay theorem in its own Lean process before committing to a full replay. This separates the initial experimental check from the old four-theorem warm-up. Record resource use and the exact checked theorem rather than inferring success from module generation.

Logical confidence in this construction and its paired induction is high. Its elimination of persistent initial insertions is a structural fact. Peak memory and runtime remain unmeasured: direct recursive construction, wide masks, checkpoint comparisons and replay may still require substantial resources. No speed or memory-fit claim is made.

## Inspected evidence

All paths below are relative to milestone144, except the generator path.

| File | SHA-256 |
| --- | --- |
| `data/warmup-stop.json` | `a4b5f908af976b7dbf64f80406d99c16c8232ff95a24c825d4b6d71840390c93` |
| `data/proof-plan-base.json` | `f398fcd7276e16732723e015cd127d2bc372b270912bfa95d68e40c7c866f2ec` |
| `lean/LocalWindowUnsat/ShareWindow144/Data0.lean` | `581477014994364b4ee56126cb5ed9a9c266b6288c1000fefe074081302fd0df` |
| `lean/LocalWindowUnsat/ShareWindow144/Check1.lean` | `e961831ec18a0f561067df7cc8fd679cbdfd03cb40a9b998cfb46b7ad40df757` |
| `lean/LratFast144.lean` | `f0101d53f2c2651e585f31938e0b5be7b82de49f7ee7c27333b6112116ace56c` |
| `lean/LratCheck144.lean` | `09f164a49d9511205d60292c64b1db4509ef34b82c131d0a4ecda8a3977c005b` |
| `milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py` | `2f4b1339817194163a080468d2e404dd7d14e7c048f8fc90e0a2691b243bf384` |

Only this diagnosis note was created. No existing source, plan, proof, receipt or log was modified, and no Lean compiler, solver or full-graph computation was launched.
