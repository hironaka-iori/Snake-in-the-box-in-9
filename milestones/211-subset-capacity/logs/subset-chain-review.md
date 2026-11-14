# Subset-capacity continuation-chain review

Date: 2026-11-14. Result: all 196 new accepted transitions reconstruct exactly from the fixed transfer through the frozen final state. No discrepancy was found. This is an independent inspection of saved native records and their state updates. No search, compiler, Lean run, software test, or process operation was performed.

## Complete transition inspection

Starting with `data/case-23/initial-state.json`, the review followed receipt indices 100 through 295 in their exact final-state order. For every transition it independently verified:

- Before-state bytes equal the preceding after-state bytes, with matching receipt hashes and job counts.
- The selected job is the last saved frontier entry, with the recorded ID and complete input domain vector.
- The input header has the original model's dimensions, relations, nogoods and permutations; its domain vector is the selected region. Every job specifies 3.0 seconds and 100,000,000 nodes.
- SHA-256 of the exact input header followed by the unchanged input tail agrees with the receipt. Output bytes agree with the recorded output hash.
- All seven engine pins and four model pins agree with the fixed transferred state and their actual files. The ordered 100-receipt inherited prefix is unchanged.
- Every accepted job has exit code zero, no hard stop, and consistent status, node/time values and returned-region count. There is no witness output.
- Every returned region has 81 nonempty domains contained in its selected parent domain vector. All 698 returned-region pair comparisons show disjoint Cartesian regions: at least one coordinate has disjoint masks. The complete saved frontier is also pairwise disjoint after every update, with unique region IDs.
- Independently rebuilding the state by removing the selected entry, assigning consecutive new IDs, appending returned regions in reverse order, updating counters, and appending exactly one receipt reproduces the complete saved after-state bytes and hash. All other fields, including the transfer reference, remain unchanged.

There are exactly 296 receipt files under this case directory, matching the final receipt list. The last reconstructed state equals the frozen `state.json` byte for byte, whose hash was reread at the end. Both saved batch summaries point to the reconstructed states at jobs 200 and 296 and use the same engine pins.

## Recorded results

The 196 new jobs comprise 170 `EXHAUSTED` subtree results and 26 `LIMIT` results. They return 200 regions in total, so the region-count change is \(7-196+200=11\). The native engine visits 1,038,016 additional nodes and records 115.378 additional seconds, rounded to the saved millisecond precision. These are search-work figures, without a controlled performance comparison.

| Counter over the 196 new jobs | Total |
|---|---:|
| Removed domain values | 106,327,203 |
| Lexicographic removals | 14 |
| Singleton-capacity removals | 1,237,205 |
| Partner-support removals | 4,779,466 |
| Old capacity failures | 440,994 |
| Subset propagation calls | 867,316 |
| Subset removals | 5,022,135 |
| Subset failures | 84,079 |
| Tight-set encounters | 25,063,584 |

The final state remains OPEN, with 296 total committed jobs, 3,721,372 total nodes, recorded floating-point seconds `361.03300000000036`, next ID 307, and 11 pending regions. Their IDs in saved order are 13, 12, 306, 305, 304, 303, 302, 301, 300, 299, 298. Neither the case nor the full model has been exhausted.

## Memory-stop boundary and retained regions

All recorded startup gates satisfy the 1 GiB free-memory threshold and report no resource-query errors or observed Lean processes. The minimum startup free memory is 1,306,603,520 bytes; maximum recorded native private memory is 9,850,880 bytes.

The only recorded resource stop occurs in receipt index 295, for selected region 221. Its final sample records 672,219,136 free bytes, below the 768 MiB reserve, and 9,732,096 native private bytes. The saved STOP marker contains `LOW_FREE_MEMORY`. The engine exits zero without a hard stop, producing a valid `LIMIT` record with nine pending regions. Its recorded 3.016 seconds also reaches the ordinary 3-second budget; the records do not identify which internal stopping condition caused the return.

Before that job, the frontier was IDs 13, 12, 221. The accepted replacement retains the first two entries exactly and substitutes the nine contained, pairwise-disjoint returned regions for 221. All nine are preserved in the final state. The second batch therefore records 96 committed jobs, of which 95 count toward its `new_committed_jobs_without_resource_stop` field. This distinction agrees with the wrapper's counter convention.

Containment, disjointness and exact state replacement are independently established by this audit. Coverage of all unvisited satisfying assignments still depends on the reviewed native traversal and sound pruning; the audit does not independently enumerate those assignments or provide a Lean traversal certificate. The memory-stop record is retained as an unfinished search, with no exclusion inferred from it.

## SHA-256 pins

Paths below are relative to `E:/Snake-in-a-box/milestones/211-subset-capacity/`.

| Artifact | SHA-256 |
|---|---|
| `data/case-23/initial-state.json` | `6d1487feec1c8ac398493d76a9ea491113d55f779cacb399fc9ad2822fcf5883` |
| `data/case-23/state.json` | `3b7733ba9ad904608c050ed63199b13a295c56db6d3b1ded909ef13be38d5e7d` |
| `data/frontier-transfer.json` | `f7cf9328de2e9838bcb8c727962aebad8ce0efd7ee4a037125f7782013ebef9c` |
| `scripts/capacity_solver.c` | `54aef14e94221646ffe5851a7e4ec0a6a43700bbc1f4f66c024f5dc51f6aeea4` |
| `scripts/capacity_continue.py` | `3a4456d34ce204769201c50c19cd35a2c71804698c449358e7f083a2dc992e46` |
| `build/capacity_solver.exe` | `08b74acdbbf7f8848dc44c774e4e58574e535f46eb4237089e7b7d23452b6ffb` |
| `data/capacity-batch-1794663249632962000.json` | `33ed12faba6b6c260bc3fbd04fd80d6ed2a9debe35bf465f67c0931de1485a45` |
| `data/capacity-batch-1794663367108497000.json` | `1c55876e34ca889007c10d31a564ff858d80d83cffec71ba882ac80496b8796d` |
| `data/case-23/run-295-1794663363641346300/receipt.json` | `b1e3b75f1f8af0db57ed1b838ddd734c16ecfd625cccc26b9087c03787372782` |
| `data/case-23/run-295-1794663363641346300/stdout.json` | `f5d511c80fceeb69ae09881eba5212db0a9f7e95c4dd56e8bf63473f5fe5d330` |
| `logs/subset-engine-review.md` | `639074a2086fcdd883c4eef13c2ee18da29786882e2869bb0314aae7695f5b1c` |
| `logs/frontier-transfer-review.md` | `61d8193bde7768aea40bd08aca934ee303c78722f4b25c783382a5f524dc9483` |

The previous source and transfer reviews remain unchanged. This report adds saved-transition consistency; it makes no new actual-snake or global-bound claim.
