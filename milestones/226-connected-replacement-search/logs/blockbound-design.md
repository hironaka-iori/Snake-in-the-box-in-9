# Summed block-chain length bound

New worker: `scripts/connected_blockbound.py`, SHA-256 `85aebb4de8fc177c43011b1a452a65c3213ee790f115b8ccd40bd0240c9dcf08`.

Preserved predecessor: `scripts/connected_blockchain.py`, SHA-256 `511ed6cde751886ad0bbb38156e7d2254becade7785a70c3293e99eef3f6d5d2`. Existing workers and checkpoints were not modified. The new worker has not been executed, compiled or tested.

## Change

After all original component checks and both block-chain size and colour checks pass, reject a first prefix when the existing helper's `upper_edges` is smaller than the prescribed second-path width. The counter `second_domain_prefix_prunes.BLOCKCHAIN_LENGTH` records these additional rejections. It therefore counts failures not already found by those earlier capacity checks.

The helper, all preceding search rules, allocation scope, checkpoint procedure and final witness audit are unchanged. The new worker identity, source hash and block-chain predecessor pin prevent use of an earlier worker's checkpoint. A fresh search and output tag are required.

## Necessary length bound

Fix the second residual graph after deleting the first prefix and its closed neighborhood. Any valid second path is simple and induced in this graph. By the block-chain argument in `blockchain-design.md`, it traverses only the blocks on the anchor-to-anchor incidence-tree route. In each such block it has a segment from that block's entry vertex to its exit vertex. These vertices are distinct.

If entry and exit are adjacent, the segment must have exactly one edge: otherwise their edge joins two nonconsecutive vertices of the induced path.

Otherwise use the cube's bipartition. If the entry and exit have opposite colours and the segment has $2t+1$ edges, it uses $t+1$ vertices of each colour. With $E$ even and $O$ odd vertices available in the block,

$$2t+1\le 2\min(E,O)-1.$$

If the entry and exit have the same colour and the segment has $2t$ edges, it uses $t+1$ vertices of the entry colour and $t$ of the other colour. Writing $S$ and $T$ for the corresponding block counts,

$$2t\le 2\min(S-1,T).$$

Every chain block contributes one such segment. Consecutive segments share their articulation endpoint, and their edge sets partition the full path's edges. Their edge lengths therefore add without a subtraction. Summing the bounds above gives the helper's `upper_edges`. If this sum is less than the requested width, no such second path exists for the current prefix or any extension of that prefix. This conclusion is necessary-only and does not assert that the summed bound is attainable.

## Existing Lean evidence and remaining gap

Milestone 194 contains `lean/Pruning194.lean` with reusable results:

- `Pruning194.adjacentAnchors`: a positive-length induced path with adjacent endpoints has one edge.
- `Pruning194.equalColourBound`: the same-colour arithmetic inequality under the two vertex-count premises.
- `Pruning194.oppositeColourBound`: the opposite-colour arithmetic inequality under the two vertex-count premises.
- `Pruning194.singleAttachmentObstruction`: entering and leaving a singly attached region contradicts path injectivity.

The saved accepted receipt is `milestones/194-targeted-extensions/data/Pruning194-audit.json`, SHA-256 `1268be3851284b5552caa1fba81f98698dfe977dd85d423cbb7b5ae2471f8051`. It records exit code zero and five theorem reports using only `propext` and `Quot.sound` (including the separate low-degree lemma). This review read the statements and checked current source, compiler-log and object hashes against the receipt:

- Source: `dc3bb92a06b6042c31acd085503ad4ed1878a5e4463125b351099fefe740a6c2`.
- Log `logs/Pruning194-1794449686195101200/compiler.log`: `7e0b14f57f24e57ce59ddfabb005f5095cb5f48f3e974c879151a92ddde538f6`.
- Object `build/Pruning194.olean`: `129c9f13a7d7638fbab2661889c89213f13cd01f66e7e6d2bcd600377a3a0ed9`.

No Lean rebuild was performed here. Those lemmas do not check the Python low-link decomposition or establish that its returned chain partitions every actual anchor path into the asserted block segments. A complete transfer still needs that decomposition/path statement, derivation of each segment's bipartite count premises, and an edge-length summation theorem tied to the returned finite data. Native DFS coverage and checkpoint completeness also remain outside this Lean evidence. Accordingly, the new worker's exclusions would remain restricted native enumeration results.
