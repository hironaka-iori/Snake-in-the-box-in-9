# Round 226 block-length and face-capacity review

Conclusion: the added block-length rejection is a necessary condition for the second induced path. Every saved face-capacity record agrees with an independent recount of its literal prepared domain. No invalid exclusion was identified. The fresh case-114 run ended at its time limit and supplies no exclusion.

## Source scope and identities

Read the complete diff from the already reviewed `connected_blockchain.py` to `connected_blockbound.py`, and the complete `logs/blockbound-design.md`. The new worker has 431 lines and SHA256 `85aebb4de8fc177c43011b1a452a65c3213ee790f115b8ccd40bd0240c9dcf08`. Its predecessor remains `511ed6cde751886ad0bbb38156e7d2254becade7785a70c3293e99eef3f6d5d2`. The design note hashes to `c05b9681fbd4d12ffdce4df65a89f4fa3020683ce1dacdfe03f93aeca27f9efa`.

The only new pruning rule is `chain['upper_edges'] < width`, after the previous component and block-chain size/colour checks. The remaining changes identify the new worker, pin its predecessor, and add the `BLOCKCHAIN_LENGTH` counter. The historical helper and all other top-level helper functions are unchanged. Earlier search rules, checkpoint transitions and witness reconstruction are unchanged in the complete diff.

## Necessity of the summed bound

The previous review establishes that every simple path between the second anchors stays in the blocks on their incidence-tree route. Its intersection with each successive block is one segment between that block's distinct entry and exit vertices. Leaving a block through a side attachment and returning, or revisiting a block after proceeding through the chain, would repeat an articulation vertex. Each segment inherits inducedness from the complete path.

If entry and exit are adjacent, its segment has exactly one edge. Any longer segment would contain the entry-exit edge as a chord. Otherwise, write \(E,O\) for the two cube-parity counts in the block. A segment with opposite-parity endpoints and \(2t+1\) edges needs \(t+1\) vertices of each parity, so

\[
2t+1\le 2\min(E,O)-1.
\]

For equal-parity endpoints, let \(S\) be the number of available vertices of their parity and \(T\) the other count. A segment with \(2t\) edges needs \(t+1\) and \(t\) vertices respectively, so

\[
2t\le 2\min(S-1,T).
\]

These are precisely the helper's three cases. Counting every vertex of a retained block may overestimate available capacity, which is safe for this upper bound. Successive segments share an articulation vertex, while their edges partition the complete path's edges; their edge lengths therefore add directly. The sum is an upper bound, without an attainment claim.

Any completion of a first prefix leaves its second path in the current residual graph. Consequently, if the current summed upper bound is below the required width, no extension of that first prefix can supply the second path. This implication does not require the numeric bound itself to decrease under every later deletion.

The new worker's source/identity pins reject predecessor checkpoints. It starts fresh for context 114, original first part zero, first crossing count zero, with derived allocation (0,1). Its same-source future checkpoints retain the existing allocation scope. The historical Lean lemmas cited in the design note do not certify the Python decomposition, its concrete path-segment interpretation, numeric assembly or DFS traversal; this review does not claim such a certificate or repeat the old Lean receipt audit.

## Independent face recount

`data/face-capacity.json` hashes to `dd16ccd792c0a83e67199dc1c3eea8a73499fffbec39d7790a745ffc1a85dfe5`. Its source pin matches `data/regions43.json`, SHA256 `b1cf54d596bcd8e04162fef9741dca90eed03ab03e78089318614215d1b9b3da`.

Read every saved row and independently filtered each literal second domain by the coordinate-8 bit of its first anchor. The complete sorted vertex lists, anchor pairs, same-face flags, counts, targets, crossing budgets and size-exclusion flags all match. There are no missing or duplicated IDs among the 25 originally unresolved contexts.

- IDs 22–27, 64–69 and 106–111 have 13 vertices in the common second-anchor face: 18 cases.
- IDs 28, 29, 70, 71, 112 and 113 have 14: six cases.
- ID114 has opposite-face anchors 35 and 462; its first-anchor-face count is 92. Its size-exclusion flag is correctly false.

Each ordinary second replacement needs 44 distinct vertices. With zero coordinate-8 crossings, all would remain in its anchor face, contradicting the count 13 or 14. Hence its crossing count is positive; equal endpoint bits make that count even. Since the combined budget is two, the second count is two and the first count is zero. Thus these exact domain counts independently exclude allocation (2,0) and force (0,2), without depending on that allocation's solver result. This remains conditional on the separately audited validity of the prepared domains.

For ID114, opposite second-anchor bits require an odd count and the total budget is one, so (0,1) is forced by endpoint parity. The ordinary same-face capacity argument is not applied to this exception.

## Terminal run and preserved checkpoints

The fresh `block43-114` run became terminal during this review. Its receipt records accepted exit zero without a stop reason; its search result is `TIME_LIMIT`, not exhaustion. It records 60 seconds, 389,897 processed first prefixes, zero complete first paths, zero second prefixes, no witness, and 12 pending first prefixes. The additional block-chain counts are 61,906 size rejections, 13,162 colour rejections and 12,176 length rejections. These counters do not establish a measured overall speedup.

Recomputed worker/input/result pins and the checkpoint hash match; checkpoint counts and pending-frontier lengths agree with the result. The result explicitly has both exclusion flags false.

| Artifact | SHA256 |
|---|---|
| `data/block43-114/result.json` | `78f3a85d02565647049c566d4865c0fa3e6ba70fdf468f340d0267a881b7a547` |
| `data/block43-114-execution.json` | `c1bb422f4b29c91c9018da476b600fa12e17422c9d7c3a78fb1855146525b0ad` |
| `data/block43-114/checkpoint.json` | `cb7506b0101512377f0b4a830519fd61d6183fa40dbeaa5ac706a017b4b4af47` |

The original round-225 context-22 checkpoint remains `3505cc1bda640fa6d16db2f7ec1d260229b35637090ead5360ed57917caadf3c`; the pruned checkpoint remains `6777944b1c9562355c9e09a4ca258bf0da33900007b93619037c5e716c0aa1ba`; the transferred copy remains `28c3530c14e63f97caf55c0a3c98680df29f0381f42fc73e505e3a2ed75dd657`. Their searches remain historically incomplete even though separate native solver results now exclude context 22.

The design note's statement that the new worker has not been executed describes preparation time; the terminal receipt now supersedes it. The final round account should retain that historical qualification. No source or checkpoint was changed here. No solver, compiler or software test was run, and no new global bound is claimed.
